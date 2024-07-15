package main

import (
	"bytes"
	"container/heap"
	"encoding/gob"
	"errors"
	"fmt"
	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	mapset "github.com/deckarep/golang-set/v2"
	"golang.org/x/exp/slices"
	"gonum.org/v1/gonum/mat"
	"log"
	"math"
	"math/big"
	"math/rand"
	"os"
	"path/filepath"
	"reflect"
	"strconv"
	"testing"
	"time"
)

const inputsizeconst = 14 //adult:14, credit:23, german: 20
const penultlayersize = 2 //if 8_4 then 4 is the penult
const maxheapsize = 31

const numlayersconst = 2
const outlogits = 2
const roundingpower = 3
const roundingcoeff = 10
const sensitiveattributeind = 0

type layer_sizes_dict struct {
	LayerSizes []int `json:"layer_sizes"`
}
type code_pt_dict struct {
	PointPolytopeList []codept `json:"point_polytope_list"`
}
type codept struct {
	Code string    `json:"Code"`
	Pt   []float64 `json:"Pt"`
}
type code struct {
	ActivationCode string `json:"activation_code"`
}
type facetpt struct {
	PerPolyListWithPt []struct {
		PolytopeConfig string          `json:"polytope_config"`
		NormalFacets   [][]interface{} `json:"normal"`
		DecisionFacets [][]interface{} `json:"decision"`
	} `json:"per_poly_list_with_pt"`
}
type polytope_general struct {
	A        *mat.Dense
	b        *mat.VecDense
	code     string
	fullcode string
}
type input struct {
	InputPoint []float64 `json:"input_point"`
}
type facet_general struct {
	a                    *mat.VecDense
	b                    float64
	fType                string
	polywhichcreated     string
	polywhichcreatedfull string
	tight                int
	dec_pt               *mat.VecDense
	linearmapa           *mat.Dense
	linearmapb           *mat.VecDense
}
type limits struct {
	FacetcheckDecision        int   `json:"facetcheck_decision"`
	FacetcheckNormal          int   `json:"facetcheck_normal"`
	PointonfacetcheckDecision int   `json:"pointonfacetcheck_decision"`
	PointonfacetcheckNormal   int   `json:"pointonfacetcheck_normal"`
	ProjectionNormalInit      int64 `json:"projection_normal_init"`
	ProjectionNormalOther     int64 `json:"projection_normal_other"`
	ProjectionDecisionInit    int64 `json:"projection_decision_init"`
	ProjectionDecisionOther   int64 `json:"projection_decision_other"`
}
type RadiusData struct {
	Radius float64 `json:"Radius"`
}
type Xorcircuit struct {
	Rold     [inputsizeconst * numlayersconst]frontend.Variable `gnark:"Rold"`
	Rnew     [inputsizeconst * numlayersconst]frontend.Variable `gnark:"Rnew"`
	Facetind frontend.Variable                                  `gnark:"Facetind"`
}
type VerifyHeapPop struct {
	List    [maxheapsize]frontend.Variable `gnark:"List"`
	MinItem frontend.Variable              `gnark:"MinItem"`
}
type VerifyRadiimin struct {
	RadiiList [2]frontend.Variable `gnark:"RadiiList"`
	MinItem   frontend.Variable    `gnark:"MinItem"`
}
type VerifyDecisionFacetCheck struct {
	Pt               [inputsizeconst]frontend.Variable `gnark:"Pt"`
	LinearMapA0      [inputsizeconst]frontend.Variable `gnark:"LinearMapA0"`
	LinearMapA1      [inputsizeconst]frontend.Variable `gnark:"LinearMapA1"`
	LinearMapB0      frontend.Variable                 `gnark:"LinearMapB0"`
	LinearMapB1      frontend.Variable                 `gnark:"LinearMapB1"`
	Limit            frontend.Variable                 `gnark:"Limit"`
	Fieldminusoneby2 frontend.Variable                 `gnark:"Fieldminusoneby2"`
}
type VerifyNormalFacetCheck struct {
	Pt          [inputsizeconst]frontend.Variable `gnark:"Pt"`
	LinearMapA0 [inputsizeconst]frontend.Variable `gnark:"LinearMapA0"`
	LinearMapA1 [inputsizeconst]frontend.Variable `gnark:"LinearMapA1"`
	LinearMapB0 frontend.Variable                 `gnark:"LinearMapB0"`
	LinearMapB1 frontend.Variable                 `gnark:"LinearMapB1"`
	Limit       frontend.Variable                 `gnark:"Limit"`
}
type VerifyPointOnFacet struct {
	Facet_eq_A       [inputsizeconst]frontend.Variable                                    `gnark:"FacetAeq"`
	Facet_eq_B       frontend.Variable                                                    `gnark:"FacetBeq"`
	Pt               [inputsizeconst]frontend.Variable                                    `gnark:"Pt"`
	Limitsq_eq       frontend.Variable                                                    `gnark:"Limiteq"`
	Facet_ineq_A     [(inputsizeconst * numlayersconst)][inputsizeconst]frontend.Variable `gnark:"FacetAineq"`
	Facet_ineq_B     [(inputsizeconst * numlayersconst)]frontend.Variable                 `gnark:"FacetBineq"`
	Fieldminusoneby2 frontend.Variable                                                    `gnark:"Fieldminusoneby2"`
}
type verifyprojection struct {
	Ca                [inputsizeconst]frontend.Variable     `gnark:"a"`
	Ca_abs            [inputsizeconst - 1]frontend.Variable `gnark:"a_abs"`
	Cb_extra_scaled   frontend.Variable                     `gnark:"b_extra_scaled"`
	Cx0               [inputsizeconst]frontend.Variable     `gnark:"x0"`
	Cprojsq           frontend.Variable                     `gnark:"Cprojsq"`
	Limitsq_eq        frontend.Variable                     `gnark:"Limit"`
	CFieldminusoneby2 frontend.Variable                     `gnark:"CFieldminusoneby2"`
}
type VerifyMakeAdvConstraints struct {
	Truelabelb    frontend.Variable                 `gnark:"Truelabelb"`
	NotTruelabelb frontend.Variable                 `gnark:"NotTruelabelb"`
	Truelabela    [inputsizeconst]frontend.Variable `gnark:"Truelabela"`
	NotTruelabela [inputsizeconst]frontend.Variable `gnark:"NotTruelabela"`
	AdvA          [inputsizeconst]frontend.Variable `gnark:"AdvA"`
	AdvB          frontend.Variable                 `gnark:"AdvB"`
}
type verifyactivationcode struct {
	Callweights          [numlayersconst][inputsizeconst][inputsizeconst]frontend.Variable `gnark:"Callweights"`
	Callbiases           [numlayersconst][inputsizeconst]frontend.Variable                 `gnark:"Callbiases"`
	Cx                   [inputsizeconst]frontend.Variable                                 `gnark:"Cx"`
	Chidden_layer_size   [numlayersconst]frontend.Variable                                 `gnark:"Chidden_layer_size"`
	Actcodearray         [numlayersconst][inputsizeconst]frontend.Variable                 `gnark:"Actcodearray"`
	FieldSizeminusone    frontend.Variable                                                 `gnark:"FieldSizeminusone"`
	FieldSizeminusoneby2 frontend.Variable                                                 `gnark:"FieldSizeminusoneby2"`
}
type verifyinference struct {
	Callweightsfull [numlayersconst + 1][inputsizeconst][inputsizeconst]frontend.Variable `gnark:"allweightsfull"`
	Callbiasesfull  [numlayersconst + 1][inputsizeconst]frontend.Variable                 `gnark:"allbiasesfull"`
	Cx              [inputsizeconst]frontend.Variable                                     `gnark:"Cx"`
	//Chidden_layer_sizefull [numlayersconst + 1]frontend.Variable                                 `gnark:"chidden_layer_sizefull"`
	Cfout frontend.Variable `gnark:"coutput"`
}
type verifypolytope struct {
	Cactcodearray [numlayersconst][inputsizeconst]frontend.Variable                  `gnark:"Cactcodearray"`
	Callweights   [numlayersconst][inputsizeconst][inputsizeconst]frontend.Variable  `gnark:"allweights"`
	Callbiases    [numlayersconst][inputsizeconst]frontend.Variable                  `gnark:"allbiases"`
	PolyA         [inputsizeconst * numlayersconst][inputsizeconst]frontend.Variable `gnark:"polyA"`
	Polyb         [inputsizeconst * numlayersconst]frontend.Variable                 `gnark:"polyb"`
}
type verifyinference_small struct {
	CWeightslast      [outlogits][penultlayersize]frontend.Variable `gnark:"CWeightslast"`
	CBiaseslast       [outlogits]frontend.Variable                  `gnark:"CBiaseslast"`
	Cpenult           [penultlayersize]frontend.Variable            `gnark:"Cpenult"`
	Clargerlogitind   [outlogits]frontend.Variable                  `gnark:"Clarge"`
	CFieldminusoneby2 frontend.Variable                             `gnark:"CFieldminusoneby2"`
}

func (circuit *VerifyHeapPop) Define(api frontend.API) error {
	for j := 0; j < len(circuit.List); j++ {
		//api.Println("jth element: ", j, circuit.List[j])
		api.AssertIsLessOrEqual(circuit.MinItem, circuit.List[j])
	}
	return nil
}
func (circuit *VerifyRadiimin) Define(api frontend.API) error {
	for j := 0; j < len(circuit.RadiiList); j++ {
		//api.Println("jth element: ", j, circuit.List[j])
		api.AssertIsLessOrEqual(circuit.MinItem, circuit.RadiiList[j])
	}
	return nil
}
func (circuit *verifyprojection) Define(api frontend.API) error {
	ax := dotpdtf(api, circuit.Ca, circuit.Cx0)
	num := api.Sub(circuit.Cb_extra_scaled, ax)
	numsq := api.Mul(num, num)
	denom := dotpdtfsmallsize(api, circuit.Ca_abs, circuit.Ca_abs) //getting squared from norm, should've been multiplied by 10^6 but we dont as we already feed that 10^6 in the proj supplied here

	lhs_sq := api.Mul(circuit.Cprojsq, denom)

	upperlimit := api.Add(circuit.CFieldminusoneby2, circuit.Limitsq_eq)
	lowerlimit := api.Sub(circuit.CFieldminusoneby2, circuit.Limitsq_eq)

	val := api.Sub(lhs_sq, numsq)
	val = api.Add(val, circuit.CFieldminusoneby2)

	api.AssertIsLessOrEqual(lowerlimit, val)
	api.AssertIsLessOrEqual(val, upperlimit)
	return nil
}
func (circuit *VerifyPointOnFacet) Define(api frontend.API) error {
	upperlimit := api.Add(circuit.Fieldminusoneby2, circuit.Limitsq_eq)
	lowerlimit := api.Sub(circuit.Fieldminusoneby2, circuit.Limitsq_eq)

	dpt := dotpdtf(api, circuit.Facet_eq_A, circuit.Pt)
	val := api.Sub(dpt, circuit.Facet_eq_B)
	val = api.Add(val, circuit.Fieldminusoneby2)
	api.AssertIsLessOrEqual(lowerlimit, val)
	api.AssertIsLessOrEqual(val, upperlimit)

	for i := 0; i < len(circuit.Facet_ineq_B); i++ {
		dpt = dotpdtf(api, circuit.Facet_ineq_A[i], circuit.Pt)
		val = api.Sub(dpt, circuit.Facet_ineq_B[i])
		valfinal := api.Add(val, circuit.Fieldminusoneby2)
		api.AssertIsLessOrEqual(valfinal, upperlimit)
	}
	return nil
}
func (circuit *VerifyDecisionFacetCheck) Define(api frontend.API) error {

	upperlimit := api.Add(circuit.Fieldminusoneby2, circuit.Limit)
	lowerlimit := api.Sub(circuit.Fieldminusoneby2, circuit.Limit)

	out0 := api.Add(dotpdtf(api, circuit.LinearMapA0, circuit.Pt), circuit.LinearMapB0)
	out1 := api.Add(dotpdtf(api, circuit.LinearMapA1, circuit.Pt), circuit.LinearMapB1)
	diff := api.Sub(out1, out0)

	diff = api.Add(diff, circuit.Fieldminusoneby2)

	api.AssertIsLessOrEqual(lowerlimit, diff)
	api.AssertIsLessOrEqual(diff, upperlimit)
	return nil
}
func (circuit *VerifyNormalFacetCheck) Define(api frontend.API) error {
	out0 := api.Add(dotpdtf(api, circuit.LinearMapA0, circuit.Pt), circuit.LinearMapB0)
	out1 := api.Add(dotpdtf(api, circuit.LinearMapA1, circuit.Pt), circuit.LinearMapB1)
	diff := api.Sub(out1, out0)
	api.AssertIsLessOrEqual(circuit.Limit, diff)
	return nil
}
func (circuit *VerifyMakeAdvConstraints) Define(api frontend.API) error {
	var temp_val frontend.Variable

	for j := 0; j < inputsizeconst; j++ {
		temp_val = api.Sub(circuit.Truelabela[j], circuit.NotTruelabela[j]) //dec_bound_a
		api.AssertIsEqual(circuit.AdvA[j], temp_val)
	}
	dec_bound_b := api.Sub(circuit.NotTruelabelb, circuit.Truelabelb)
	api.AssertIsEqual(circuit.AdvB, dec_bound_b)
	return nil
}
func (circuit *Xorcircuit) Define(api frontend.API) error {
	var tempsum frontend.Variable

	tempsum = 0
	for i := 0; i < len(circuit.Rold); i++ {
		tempxor := api.Xor(circuit.Rold[i], circuit.Rnew[i])
		tempsum = api.Add(tempsum, tempxor)
		tempind := api.Select(api.IsZero(api.Sub(frontend.Variable(i), circuit.Facetind)), frontend.Variable(1), frontend.Variable(0))
		api.AssertIsEqual(tempind, tempxor)
	}
	api.AssertIsEqual(tempsum, 1)
	return nil
}
func (circuit *verifypolytope) Define(api frontend.API) error {
	var CpolyA [inputsizeconst * numlayersconst][inputsizeconst]frontend.Variable
	var Cpolyb [inputsizeconst * numlayersconst]frontend.Variable

	var wks [numlayersconst][inputsizeconst][inputsizeconst]frontend.Variable
	var bks [numlayersconst][inputsizeconst]frontend.Variable

	wks[0] = circuit.Callweights[0]
	bks[0] = circuit.Callbiases[0]

	for i := 1; i < numlayersconst; i++ {
		var current_wk [inputsizeconst][inputsizeconst]frontend.Variable
		var current_bk [inputsizeconst]frontend.Variable
		var float_activation_code [inputsizeconst]frontend.Variable
		var precomute [inputsizeconst][inputsizeconst]frontend.Variable
		var current_lambda [inputsizeconst][inputsizeconst]frontend.Variable
		var wb [inputsizeconst]frontend.Variable
		var final_b [inputsizeconst]frontend.Variable
		var new_wk [inputsizeconst][inputsizeconst]frontend.Variable

		current_wk = wks[i-1]
		current_bk = bks[i-1]
		for j := 0; j < len(circuit.Cactcodearray[i-1]); j++ {
			float_activation_code[j] = circuit.Cactcodearray[i-1][j]
		}

		current_lambda = creatediagonalmatrix(api, float_activation_code)
		precomute = matrixmul(api, circuit.Callweights[i], current_lambda)
		new_wk = matrixmul(api, precomute, current_wk)
		wks[i] = new_wk

		wb = MulVecf(api, precomute, current_bk)
		final_b = AddVecf(api, wb, circuit.Callbiases[i])
		bks[i] = final_b
	}

	count := 0 //check this

	for i := 0; i < len(wks); i++ {
		current_wk := wks[i]
		current_bk := bks[i]

		shifted_activation_code := [inputsizeconst]frontend.Variable{}
		for j := 0; j < len(circuit.Cactcodearray[i]); j++ {
			shifted_activation_code[j] = api.Add(api.Mul(frontend.Variable(-2), circuit.Cactcodearray[i][j]), frontend.Variable(1))
		}

		current_j := creatediagonalmatrix(api, shifted_activation_code)
		scaled_current_j := scalematrix(api, frontend.Variable(-1), current_j)

		a_to_stack := matrixmul(api, current_j, current_wk)
		b_to_stack := MulVecf(api, scaled_current_j, current_bk)

		for k := 0; k < len(a_to_stack); k++ {
			CpolyA[count] = a_to_stack[k]
			Cpolyb[count] = b_to_stack[k]
			count += 1 //check this
		}
	}

	for i := 0; i < inputsizeconst*numlayersconst; i++ { //24 *3
		api.AssertIsEqual(circuit.Polyb[i], Cpolyb[i])
	}

	for i := 0; i < inputsizeconst*numlayersconst; i++ { //24 *3
		for j := 0; j < inputsizeconst; j++ {
			api.AssertIsEqual(circuit.PolyA[i][j], CpolyA[i][j])
		}
	}

	for i := 0; i < numlayersconst; i++ {
		for j := 0; j < inputsizeconst; j++ {
			tempadd := api.Add(circuit.Callbiases[i][j], circuit.Cactcodearray[i][j])
			for k := 0; k < inputsizeconst; k++ {
				api.Add(circuit.Callweights[i][j][k], tempadd)
			}
		}
	}

	return nil
}
func (circuit *verifyinference_small) Define(api frontend.API) error {
	var logits [outlogits]frontend.Variable

	for i := 0; i < outlogits; i++ {
		wx := dotpdtf_small(api, circuit.CWeightslast[i], circuit.Cpenult)
		tempinp := api.Add(wx, circuit.CBiaseslast[i])
		logits[i] = api.Add(tempinp, circuit.CFieldminusoneby2)
	}

	maxelem := dotpdtf_small(api, circuit.Clargerlogitind, logits)

	for i := 0; i < outlogits; i++ {
		api.AssertIsLessOrEqual(logits[i], maxelem)
	}

	return nil
}
func (circuit *verifyactivationcode) Define(api frontend.API) error {
	var x [inputsizeconst]frontend.Variable
	var allweights [numlayersconst][inputsizeconst][inputsizeconst]frontend.Variable
	var allbiases [numlayersconst][inputsizeconst]frontend.Variable
	var activation_code_array [numlayersconst][inputsizeconst]frontend.Variable
	var tempinp [inputsizeconst]frontend.Variable

	allweights = circuit.Callweights
	allbiases = circuit.Callbiases
	x = circuit.Cx
	tempinp = x

	for hidden_layer := 0; hidden_layer < numlayersconst; hidden_layer++ {

		var temp_act_code [inputsizeconst]frontend.Variable
		var dotpdtvec [inputsizeconst]frontend.Variable
		var biassum [inputsizeconst]frontend.Variable
		var postrelu [inputsizeconst]frontend.Variable
		var vals [inputsizeconst]frontend.Variable

		dotpdtvec = MulVecf(api, allweights[hidden_layer], tempinp)
		biassum = AddVecf(api, dotpdtvec, allbiases[hidden_layer])
		for i := 0; i < inputsizeconst; i++ {

			vals[i] = api.Cmp(circuit.FieldSizeminusoneby2, biassum[i]) //check for boundary cases
			valcomp := api.IsZero(api.Sub(vals[i], circuit.FieldSizeminusone))

			postrelu[i] = api.Select(valcomp, frontend.Variable(0), biassum[i])
			temp_act_code[i] = api.Select(valcomp, frontend.Variable(0), frontend.Variable(1))
		}
		tempinp = postrelu
		activation_code_array[hidden_layer] = temp_act_code
	}

	for i := 0; i < numlayersconst; i++ {
		for j := 0; j < inputsizeconst; j++ {
			api.AssertIsEqual(circuit.Actcodearray[i][j], activation_code_array[i][j])
		}
	}
	api.Mul(circuit.Chidden_layer_size[0], circuit.Chidden_layer_size[1])
	return nil
}
func (circuit *verifyinference) Define(api frontend.API) error {
	var x [inputsizeconst]frontend.Variable
	var allweightsfull [numlayersconst + 1][inputsizeconst][inputsizeconst]frontend.Variable
	var allbiasesfull [numlayersconst + 1][inputsizeconst]frontend.Variable
	var tempinp [inputsizeconst]frontend.Variable
	var fieldsize frontend.Variable
	var minusone frontend.Variable
	allweightsfull = circuit.Callweightsfull
	allbiasesfull = circuit.Callbiasesfull
	x = circuit.Cx
	tempinp = x
	fieldsize = api.Compiler().Field()
	minusone = api.Sub(fieldsize, frontend.Variable(1))
	valsval := api.Div(minusone, frontend.Variable(2))

	for hidden_layer := 0; hidden_layer < numlayersconst+1; hidden_layer++ {

		var dotpdtvec [inputsizeconst]frontend.Variable
		var biassum [inputsizeconst]frontend.Variable
		var postrelu [inputsizeconst]frontend.Variable
		var vals [inputsizeconst]frontend.Variable

		dotpdtvec = MulVecf(api, allweightsfull[hidden_layer], tempinp)
		biassum = AddVecf(api, dotpdtvec, allbiasesfull[hidden_layer])
		for i := 0; i < inputsizeconst; i++ {
			vals[i] = api.Cmp(valsval, biassum[i]) //check for boundary cases
			valcomp := api.IsZero(api.Sub(vals[i], minusone))
			postrelu[i] = api.Select(valcomp, frontend.Variable(0), biassum[i])
		}
		tempinp = postrelu

	}
	var output frontend.Variable
	var cmp frontend.Variable

	cmp = api.Cmp(tempinp[0], tempinp[1])
	output = api.Select(cmp, frontend.Variable(0), frontend.Variable(1))

	api.AssertIsEqual(output, circuit.Cfout)
	return nil
}

/*
	func (circuit *verifyinference_small) Define(api frontend.API) error {
		var logits [outlogits]frontend.Variable

		fieldsize := api.Compiler().Field()
		fieldsize_minusone := api.Sub(fieldsize, frontend.Variable(1))
		field_mid := api.Div(fieldsize_minusone, frontend.Variable(2))
		element_minusone := api.Sub(fieldsize, frontend.Variable(2))

		for i := 0; i < outlogits; i++ {
			wx := dotpdtf_small(api, circuit.CWeightslast[i], circuit.Cpenult)
			tempinp := api.Add(wx, circuit.CBiaseslast[i])
			api.Println("logit: ", tempinp)
			logits[i] = api.Add(tempinp, field_mid)
		}

		cmpresult := api.Cmp(logits[0], logits[1])
		diff := api.IsZero(api.Sub(cmpresult, element_minusone))
		cmpresult = api.Select(diff, frontend.Variable(0), frontend.Variable(1))
		//selind := api.Select(cmpresult, frontend.Variable(0), frontend.Variable(1))
		api.AssertIsEqual(circuit.Clargerlogitind, cmpresult)
		return nil
	}
*/

func creatediagonalmatrix(api frontend.API, actcode [inputsizeconst]frontend.Variable) [inputsizeconst][inputsizeconst]frontend.Variable {
	var outmat [inputsizeconst][inputsizeconst]frontend.Variable

	for i := 0; i < len(actcode); i++ {
		for j := 0; j < len(actcode); j++ {
			outmat[i][j] = frontend.Variable(0)
		}
	}

	for i := 0; i < len(actcode); i++ {
		outmat[i][i] = actcode[i]
	}

	return outmat
}
func scalematrix(api frontend.API, scalingfac frontend.Variable, scalingmat [inputsizeconst][inputsizeconst]frontend.Variable) [inputsizeconst][inputsizeconst]frontend.Variable {
	var outmat [inputsizeconst][inputsizeconst]frontend.Variable
	for i := 0; i < len(scalingmat); i++ {
		for j := 0; j < len(scalingmat); j++ {
			outmat[i][j] = api.Mul(scalingfac, scalingmat[i][j])
		}
	}
	return outmat
}
func matrixmul(api frontend.API, matA [inputsizeconst][inputsizeconst]frontend.Variable, matB [inputsizeconst][inputsizeconst]frontend.Variable) [inputsizeconst][inputsizeconst]frontend.Variable {
	var outmat [inputsizeconst][inputsizeconst]frontend.Variable

	for i := 0; i < len(matA); i++ {
		for j := 0; j < len(matA); j++ {
			outmat[i][j] = frontend.Variable(0)
			for k := 0; k < len(matA); k++ {
				outmat[i][j] = api.Add(outmat[i][j], api.Mul(matA[i][k], matB[k][j]))
			}
		}
	}

	return outmat
}
func dotpdtf_small(api frontend.API, v1 [penultlayersize]frontend.Variable, v2 [penultlayersize]frontend.Variable) frontend.Variable {
	var tempsum frontend.Variable
	tempsum = 0
	l := len(v1)
	for i := 0; i < l; i++ {
		a := api.Mul(v1[i], v2[i])
		tempsum = api.Add(a, tempsum)
		//api.Println("printing tempsum: ", tempsum, a)
	}
	//api.Println("Tempsum: ", tempsum)
	return tempsum
}
func dotpdtf(api frontend.API, v1 [inputsizeconst]frontend.Variable, v2 [inputsizeconst]frontend.Variable) frontend.Variable {
	var tempsum frontend.Variable
	tempsum = 0
	l := len(v1)
	for i := 0; i < l; i++ {
		a := api.Mul(v1[i], v2[i])
		tempsum = api.Add(a, tempsum)
		//api.Println("printing tempsum: ", tempsum, a)
	}
	//api.Println("Tempsum: ", tempsum)
	return tempsum
}
func dotpdtfsmallsize(api frontend.API, v1 [inputsizeconst - 1]frontend.Variable, v2 [inputsizeconst - 1]frontend.Variable) frontend.Variable {
	var tempsum frontend.Variable
	tempsum = 0
	l := len(v1)
	for i := 0; i < l; i++ {
		a := api.Mul(v1[i], v2[i])
		tempsum = api.Add(a, tempsum)
		//api.Println("printing tempsum: ", tempsum, a)
	}
	//api.Println("Tempsum: ", tempsum)
	return tempsum
}
func MulVecf(api frontend.API, matrix [inputsizeconst][inputsizeconst]frontend.Variable, v [inputsizeconst]frontend.Variable) [inputsizeconst]frontend.Variable {
	var dpdtvec [inputsizeconst]frontend.Variable
	for i, vec := range matrix {
		dpdtvec[i] = dotpdtf(api, vec, v)
	}
	return dpdtvec
}
func AddVecf(api frontend.API, v1 [inputsizeconst]frontend.Variable, v2 [inputsizeconst]frontend.Variable) [inputsizeconst]frontend.Variable {
	var sumvec [inputsizeconst]frontend.Variable
	for i := 0; i < len(v1); i++ {
		sumvec[i] = api.Add(v1[i], v2[i])
	}
	return sumvec
}

func find_full_valid_indices(layersize []int) []int {
	var full_valid_index_list []int
	layersize = append(layersize, 2)
	fullnumberoflayers := numlayersconst + 1

	for i := 0; i < fullnumberoflayers; i++ {
		for j := 0; j < layersize[i]; j++ {
			full_valid_index_list = append(full_valid_index_list, j+(i*inputsizeconst))
		}

	}

	return full_valid_index_list
}
func printpq(p PriorityQueue, fullvalidinddict map[int]int, hiddenLayerSize []int, actuallayersize []int, file *os.File) {
	i := len(p) - 1
	for i > -1 {
		fmt.Fprintln(file, "Just printing: ", i, p[i].priority, fullvalidinddict[p[i].value.tight], actual_layersize_code(codetolayeredarray(p[i].value.polywhichcreated, hiddenLayerSize), actuallayersize))
		i--
	}
}
func totalneurons(hidden_layer_size []int) int {
	total_hidden_neurons := 0
	for i := 0; i < len(hidden_layer_size); i++ {
		total_hidden_neurons += hidden_layer_size[i]
	}
	return total_hidden_neurons
}
func projection_general(f facet_general, x0 *mat.VecDense) (float64, float64, float64) {
	denom_a_add := mat.NewVecDense(f.a.Len(), nil)
	denom_a_add.SetVec(sensitiveattributeind, -1*f.a.AtVec(sensitiveattributeind))
	added := mat.NewVecDense(f.a.Len(), nil)
	added.AddVec(denom_a_add, f.a)
	num := ((f.b * math.Pow(roundingcoeff, roundingpower)) - mat.Dot(f.a, x0))
	denom := (added.Norm(2) * math.Pow(roundingcoeff, roundingpower))
	proj := num / denom
	return math.Abs(proj), math.Abs(num), math.Abs(denom)
}
func projection_general_diff_check(f facet_general, x0 *mat.VecDense) {
	denom_a_add := mat.NewVecDense(f.a.Len(), nil)
	denom_a_add.SetVec(sensitiveattributeind, -1*f.a.AtVec(sensitiveattributeind))
	added := mat.NewVecDense(f.a.Len(), nil)
	added.AddVec(denom_a_add, f.a)
	num := ((f.b * math.Pow(roundingcoeff, roundingpower)) - mat.Dot(f.a, x0))
	denom := (added.Norm(2) * math.Pow(roundingcoeff, roundingpower))
	proj := num / denom

	numsq := num * num
	denomsq := denom * denom
	projsq := proj * proj
	fmt.Println("num, denom, proj: ", num, denom, proj)
	fmt.Println("numsq, denomsq, projsq: ", numsq, denomsq, projsq)
	diff := (projsq * denomsq) - numsq
	fmt.Println("Projection diff: ", diff)
}

func convert_allweights_frontendvariable(allweights []*mat.Dense) [numlayersconst][inputsizeconst][inputsizeconst]frontend.Variable {
	var allweights_fe [numlayersconst][inputsizeconst][inputsizeconst]frontend.Variable
	//allweights_fe := make([][][]frontend.Variable, len(allweights))
	for i := 0; i < len(allweights); i++ {
		row, col := allweights[i].Dims()
		//allweights_fe[i] = make([][]frontend.Variable, row)
		for r := 0; r < row; r++ {
			//allweights_fe[i][r] = make([]frontend.Variable, col)
			for c := 0; c < col; c++ {
				allweights_fe[i][r][c] = frontend.Variable(int(allweights[i].At(r, c)))
			}
		}

	}
	return allweights_fe
}
func convert_allweightsfull_frontendvariable(allweightsfull []*mat.Dense) [numlayersconst + 1][inputsizeconst][inputsizeconst]frontend.Variable {
	var allweights_fe [numlayersconst + 1][inputsizeconst][inputsizeconst]frontend.Variable
	//allweights_fe := make([][][]frontend.Variable, len(allweights))
	for i := 0; i < len(allweightsfull); i++ {
		row, col := allweightsfull[i].Dims()
		//allweights_fe[i] = make([][]frontend.Variable, row)
		for r := 0; r < row; r++ {
			//allweights_fe[i][r] = make([]frontend.Variable, col)
			for c := 0; c < col; c++ {
				allweights_fe[i][r][c] = frontend.Variable(int(allweightsfull[i].At(r, c)))
			}
		}

	}
	return allweights_fe
}

func convert_allbiases_frontendvariable(allbiases []*mat.VecDense) [numlayersconst][inputsizeconst]frontend.Variable {
	var allbiases_fe [numlayersconst][inputsizeconst]frontend.Variable
	//allbiases_fe := make([][]frontend.Variable, len(allbiases))
	for i := 0; i < len(allbiases); i++ {
		//allbiases_fe[i] = make([]frontend.Variable, allbiases[i].Len())
		for j := 0; j < allbiases[i].Len(); j++ {
			allbiases_fe[i][j] = frontend.Variable(int(allbiases[i].AtVec(j)))
		}
	}
	return allbiases_fe
}
func convert_allbiasesfull_frontendvariable(allbiasesfull []*mat.VecDense) [numlayersconst + 1][inputsizeconst]frontend.Variable {
	var allbiases_fe [numlayersconst + 1][inputsizeconst]frontend.Variable
	//allbiases_fe := make([][]frontend.Variable, len(allbiases))
	for i := 0; i < len(allbiasesfull); i++ {
		//allbiases_fe[i] = make([]frontend.Variable, allbiases[i].Len())
		for j := 0; j < allbiasesfull[i].Len(); j++ {
			allbiases_fe[i][j] = frontend.Variable(int(allbiasesfull[i].AtVec(j)))
		}
	}
	return allbiases_fe
}
func convert_intarray_frontendvariable(arr []int) [inputsizeconst]frontend.Variable {
	//arr_fe := [len(arr)]frontend.Variable{}
	var arr_fe [inputsizeconst]frontend.Variable
	for i := 0; i < len(arr); i++ {
		arr_fe[i] = frontend.Variable(arr[i])

	}
	return arr_fe
}
func convert_sizedintarray_frontendvariable(arr []int) [inputsizeconst * numlayersconst]frontend.Variable {
	//arr_fe := [len(arr)]frontend.Variable{}
	var arr_fe [numlayersconst * inputsizeconst]frontend.Variable
	for i := 0; i < len(arr); i++ {
		arr_fe[i] = frontend.Variable(arr[i])

	}
	return arr_fe
}

func convert_arrofarr_frontendvariable(arr [][]int) [numlayersconst][inputsizeconst]frontend.Variable {
	//arr_fe := make([][]frontend.Variable, len(arr))
	var arr_fe [numlayersconst][inputsizeconst]frontend.Variable
	for i := 0; i < len(arr); i++ {
		//arr_fe[i] = make([]frontend.Variable, len(arr[i]))
		for j := 0; j < len(arr[i]); j++ {
			arr_fe[i][j] = frontend.Variable(arr[i][j])
		}
	}
	return arr_fe
}
func convert_polyA_to_frontend(polyA *mat.Dense) [inputsizeconst * numlayersconst][inputsizeconst]frontend.Variable {
	var polyA_fev [inputsizeconst * numlayersconst][inputsizeconst]frontend.Variable
	row, col := polyA.Dims()
	for r := 0; r < row; r++ {
		for c := 0; c < col; c++ {
			polyA_fev[r][c] = frontend.Variable(int(math.Round(polyA.At(r, c)))) //pow not needed here
		}
	}

	return polyA_fev
}
func convert_polyb_to_frontend(polyb *mat.VecDense) [inputsizeconst * numlayersconst]frontend.Variable {
	var polyb_fev [inputsizeconst * numlayersconst]frontend.Variable
	row, _ := polyb.Dims()
	for r := 0; r < row; r++ {
		polyb_fev[r] = frontend.Variable(int(math.Round(polyb.AtVec(r)))) //pow not needed here
	}
	return polyb_fev
}
func convert_polyb_to_frontend_extra_scaling(polyb *mat.VecDense) [inputsizeconst * numlayersconst]frontend.Variable {
	var polyb_fev [inputsizeconst * numlayersconst]frontend.Variable
	row, _ := polyb.Dims()
	for r := 0; r < row; r++ {
		polyb_fev[r] = frontend.Variable(int(math.Round(polyb.AtVec(r) * math.Pow(roundingcoeff, roundingpower)))) //pow not needed here
	}
	return polyb_fev
}
func convert_vecdense_to_frontend(polyb *mat.VecDense) [inputsizeconst]frontend.Variable {
	var polyb_fev [inputsizeconst]frontend.Variable
	row, _ := polyb.Dims()
	for r := 0; r < row; r++ {
		polyb_fev[r] = frontend.Variable(int(math.Round(polyb.AtVec(r)))) //pow not needed here
	}
	return polyb_fev
}

func convert_vecdense_to_frontend_smallsize(polyb *mat.VecDense) [inputsizeconst - 1]frontend.Variable {
	var polyb_fev [inputsizeconst - 1]frontend.Variable
	row, _ := polyb.Dims()
	for r := 0; r < row; r++ {
		polyb_fev[r] = frontend.Variable(int(math.Round(polyb.AtVec(r)))) //pow not needed here
	}
	return polyb_fev
}
func convert_vecdense_to_frontend_scaling(polyb *mat.VecDense) [inputsizeconst]frontend.Variable {
	var polyb_fev [inputsizeconst]frontend.Variable
	row, _ := polyb.Dims()
	for r := 0; r < row; r++ {
		polyb_fev[r] = frontend.Variable(int(math.Round(polyb.AtVec(r) * math.Pow(roundingcoeff, roundingpower)))) //pow not needed here
	}
	return polyb_fev
}
func convert_heap_to_frontend_scaling(heaplist []float64, scalingfactor float64) [maxheapsize]frontend.Variable {
	var heap_frontend [maxheapsize]frontend.Variable
	fmt.Println("Length of heaplist : ", len(heaplist))
	if len(heaplist) > maxheapsize {
		fmt.Println("The heaplist size is more : ", len(heaplist))
	}
	for r := 0; r < len(heaplist); r++ {
		heap_frontend[r] = frontend.Variable(int(math.Round(heaplist[r] * math.Pow(roundingcoeff, roundingpower*scalingfactor)))) //pow not needed here
	}
	return heap_frontend
}
func round_pad_allweights(allweights []*mat.Dense) ([numlayersconst][inputsizeconst][inputsizeconst]int, []*mat.Dense) {
	var retmat []*mat.Dense
	var retarray [numlayersconst][inputsizeconst][inputsizeconst]int
	num := inputsizeconst

	for i := 0; i < len(allweights); i++ {
		row, col := allweights[i].Dims()
		//retarray[i] = make([][]int, 16)
		retmat = append(retmat, mat.NewDense(num, num, nil)) //mat.DenseCopyOf(allweights[i]))
		for r := 0; r < row; r++ {
			//retarray[i][r] = make([]int, 24)
			for c := 0; c < col; c++ {
				temp := allweights[i].At(r, c)

				roundedTemp := int(math.Round(temp * math.Pow(roundingcoeff, roundingpower)))
				//roundedTemp := int(math.Round(temp * math.Pow(2, 5)))
				retmat[i].Set(r, c, float64(roundedTemp))
				retarray[i][r][c] = roundedTemp

			}
		}
	}

	for i := 0; i < numlayersconst; i++ {

		row, col := allweights[i].Dims()
		//retmat[i] = retmat[i].Grow(num-row, num-col).(*mat.Dense)
		for r := row; r < num; r++ {
			for c := col; c < num; c++ {
				retarray[i][r][c] = 0
			}
		}
	}

	for i := 0; i < numlayersconst; i++ {
		for r := 0; r < num; r++ {
			for c := 0; c < num; c++ {
				if int(retmat[i].At(r, c)) != retarray[i][r][c] {
					fmt.Println("********UNEQUAL******")
				}
			}
		}
	}
	return retarray, retmat
}
func round_pad_biases(allbiases []*mat.VecDense) ([numlayersconst][inputsizeconst]int, []*mat.VecDense) {
	var retvec []*mat.VecDense
	var retarray [numlayersconst][inputsizeconst]int
	num := inputsizeconst
	for i := 0; i < len(allbiases); i++ {
		row, _ := allbiases[i].Dims()
		retvec = append(retvec, mat.NewVecDense(inputsizeconst, nil)) //append(retvec, mat.VecDenseCopyOf(allbiases[i]))
		for r := 0; r < row; r++ {
			temp := allbiases[i].AtVec(r)
			roundedTemp := int(math.Round(temp * math.Pow(roundingcoeff, roundingpower)))
			//roundedTemp := int(math.Round(temp * math.Pow(2, 5)))
			retvec[i].SetVec(r, float64(roundedTemp))
			retarray[i][r] = roundedTemp
		}
	}

	for i := 0; i < numlayersconst; i++ {
		row, _ := allbiases[i].Dims()
		for r := row; r < num; r++ {
			retarray[i][r] = 0
			retvec[i].SetVec(r, 0)
		}
	}

	for i := 0; i < numlayersconst; i++ {
		for r := 0; r < num; r++ {
			if int(retvec[i].AtVec(r)) != retarray[i][r] {
				fmt.Println("********UNEQUAL******")
			}
		}
	}
	return retarray, retvec
}
func full_round_pad_allweights(allweights []*mat.Dense) []*mat.Dense {
	var retmat []*mat.Dense

	num := inputsizeconst

	for i := 0; i < len(allweights); i++ {
		row, col := allweights[i].Dims()
		//retarray[i] = make([][]int, 16)
		retmat = append(retmat, mat.NewDense(num, num, nil)) //mat.DenseCopyOf(allweights[i]))
		for r := 0; r < row; r++ {
			//retarray[i][r] = make([]int, 24)
			for c := 0; c < col; c++ {
				temp := allweights[i].At(r, c)

				roundedTemp := int(math.Round(temp * math.Pow(roundingcoeff, roundingpower)))
				//roundedTemp := int(math.Round(temp * math.Pow(2, 5)))
				retmat[i].Set(r, c, float64(roundedTemp))

			}
		}
	}

	return retmat
}
func full_round_pad_biases(allbiases []*mat.VecDense) []*mat.VecDense {
	var retvec []*mat.VecDense

	num := inputsizeconst
	for i := 0; i < len(allbiases); i++ {
		row, _ := allbiases[i].Dims()
		retvec = append(retvec, mat.NewVecDense(inputsizeconst, nil)) //append(retvec, mat.VecDenseCopyOf(allbiases[i]))
		for r := 0; r < row; r++ {
			temp := allbiases[i].AtVec(r)
			roundedTemp := int(math.Round(temp * math.Pow(roundingcoeff, roundingpower)))
			//roundedTemp := int(math.Round(temp * math.Pow(2, 5)))
			retvec[i].SetVec(r, float64(roundedTemp))
		}
	}

	for i := 0; i < numlayersconst; i++ {
		row, _ := allbiases[i].Dims()
		for r := row; r < num; r++ {
			retvec[i].SetVec(r, 0)
		}
	}

	return retvec
}
func round_vecdense(x []float64) ([]float64, []int) {
	var roundedx []float64
	var roundedintx []int
	for i := 0; i < len(x); i++ {
		temp := int(math.Round(x[i])) //* math.Pow(roundingcoeff, roundingpower) --> need to do this but my x was already scaled
		//temp := int(math.Round(x[i] * math.Pow(2, 5)))
		roundedx = append(roundedx, float64(temp))
		roundedintx = append(roundedintx, temp)
	}
	return roundedx, roundedintx
}

func verifyNeighbor(file *os.File,
	vneighborproofsizes []int, vneighborprooftimes []time.Duration, vneighborverifytimes []time.Duration,

	code_pt_list code_pt_dict, new_poly_code string, old_poly_code string,

	allweights []*mat.Dense, allbiases []*mat.VecDense, hiddenLayerSize []int,
	t *testing.T, oldA *mat.Dense, oldb *mat.VecDense,
	newA *mat.Dense, newb *mat.VecDense, tightind int, actuallayersize []int) ([]int, []time.Duration, []time.Duration) {

	field_size := ecc.BN254.ScalarField()
	field_size_minusone := new(big.Int).Sub(field_size, big.NewInt(1))
	field_mid := new(big.Int).Div(field_size_minusone, big.NewInt(2))

	fulllayeredarray_new := codetolayeredarray(new_poly_code, hiddenLayerSize)
	actual_size_str_new_code := actual_layersize_code(fulllayeredarray_new, actuallayersize)

	newpolypt := findpointfromcode(code_pt_list, actual_size_str_new_code)
	for i := 0; i < len(newpolypt); i++ {
		newpolypt[i] = newpolypt[i] * math.Pow(roundingcoeff, roundingpower)
	}
	newpolyfx, newpolyix := round_vecdense(newpolypt)
	newpolyvecdense := mat.NewVecDense(len(newpolyix), newpolyfx)

	neighborcode_scaled_rounded_input, neighborcode_scaled_rounded_input_layered_array := findactivationcode(allweights, allbiases, hiddenLayerSize, newpolyvecdense)
	fmt.Println("scaled code: ", neighborcode_scaled_rounded_input)
	fmt.Println("givenn code: ", new_poly_code)
	fmt.Println("Verify Activation code in neighbor starting")
	var verifyneighboractcode verifyactivationcode
	assignment_verifyneighboract := verifyactivationcode{
		Callweights:          convert_allweights_frontendvariable(allweights),
		Cx:                   convert_intarray_frontendvariable(newpolyix),
		Chidden_layer_size:   [numlayersconst]frontend.Variable{inputsizeconst, inputsizeconst}, //change with size
		Callbiases:           convert_allbiases_frontendvariable(allbiases),
		Actcodearray:         convert_arrofarr_frontendvariable(neighborcode_scaled_rounded_input_layered_array),
		FieldSizeminusone:    frontend.Variable(field_size_minusone),
		FieldSizeminusoneby2: frontend.Variable(field_mid)}

	actprovetime, actverifytime, actproofsize := grothproveverify(&verifyneighboractcode, &assignment_verifyneighboract, "verifyneighbor : actcode", file)
	vneighborprooftimes = append(vneighborprooftimes, actprovetime)
	vneighborverifytimes = append(vneighborverifytimes, actverifytime)
	vneighborproofsizes = append(vneighborproofsizes, actproofsize)

	fmt.Println("Verify Activation code in neighbor end")

	fmt.Println("Verify polytope in neighbor starting")

	a, b := getpolytopefromcode(neighborcode_scaled_rounded_input_layered_array, allweights, allbiases, hiddenLayerSize, totalneurons(hiddenLayerSize), len(newpolyix))
	fmt.Println(a, b)
	var vpolyneighbor verifypolytope
	assignment_verifyneighbor := verifypolytope{Callweights: convert_allweights_frontendvariable(allweights),
		Callbiases:    convert_allbiases_frontendvariable(allbiases),
		PolyA:         convert_polyA_to_frontend(newA),
		Polyb:         convert_polyb_to_frontend(newb),
		Cactcodearray: convert_arrofarr_frontendvariable(fulllayeredarray_new)}
	vpolyprooftime, vpolyverifytime, vpolyproofsize := grothproveverify(&vpolyneighbor, &assignment_verifyneighbor, "verifyneighbor : verifypolytope", file)
	vneighborprooftimes = append(vneighborprooftimes, vpolyprooftime)
	vneighborverifytimes = append(vneighborverifytimes, vpolyverifytime)
	vneighborproofsizes = append(vneighborproofsizes, vpolyproofsize)
	fmt.Println("Verify polytope in neighbor end")

	fmt.Println("Verify xor in neighbor starting")
	var xorvar Xorcircuit
	assign_xor := Xorcircuit{Rold: convert_sizedintarray_frontendvariable(codetoflattenedarray(old_poly_code)), Rnew: convert_sizedintarray_frontendvariable(codetoflattenedarray(new_poly_code)), Facetind: frontend.Variable(tightind)}
	xorprooftime, xorverifytime, xorproofsize := grothproveverify(&xorvar, &assign_xor, "verifyneighbor : xor", file)
	vneighborprooftimes = append(vneighborprooftimes, xorprooftime)
	vneighborverifytimes = append(vneighborverifytimes, xorverifytime)
	vneighborproofsizes = append(vneighborproofsizes, xorproofsize)
	fmt.Println("Verify xor in neighbor end")

	return vneighborproofsizes, vneighborprooftimes, vneighborverifytimes
}

func findpointfromcode(code_pt_list code_pt_dict, code string) []float64 {
	var point []float64
	for i := 0; i < len(code_pt_list.PointPolytopeList); i++ {
		if code_pt_list.PointPolytopeList[i].Code == code {
			point = code_pt_list.PointPolytopeList[i].Pt
			break
		}
	}
	return point
}
func findsmallcode(validids []int, code []int) ([]int, string) {
	var retcode []int
	var strActCode string

	for i := 0; i < len(validids); i++ {
		retcode = append(retcode, code[validids[i]])
		strActCode += strconv.Itoa(code[validids[i]])
	}

	return retcode, strActCode
}

func make_adversarial_constraints(lastlayera *mat.Dense, lastlayerb *mat.VecDense, true_label int, polytope2 polytope_general) []facet_general {
	total_a := lastlayera
	total_b := lastlayerb
	num_logits, columns := total_a.Dims()

	true_a_temp := total_a.RawRowView(true_label)
	true_a := mat.NewVecDense(columns, true_a_temp)
	true_b := total_b.AtVec(true_label)
	var facets []facet_general

	for i := 0; i < num_logits; i++ {
		if i == true_label {
			continue
		} else {
			var dec_bound facet_general
			dec_bound.a = mat.NewVecDense(columns, nil)
			for j := 0; j < columns; j++ {
				temp_val := true_a.AtVec(j) - total_a.RawRowView(i)[j]
				dec_bound.a.SetVec(j, temp_val)
			}

			dec_bound.b = total_b.AtVec(i) - true_b
			dec_bound.polywhichcreated = polytope2.code
			dec_bound.polywhichcreatedfull = polytope2.fullcode
			dec_bound.fType = "decision"
			facets = append(facets, dec_bound)
		}
	}
	return facets
}

func grothproveverify(cname frontend.Circuit, assignment frontend.Circuit, circuitname string, file *os.File) (time.Duration, time.Duration, int) {
	witnesscircuit, _ := frontend.NewWitness(assignment, ecc.BN254.ScalarField()) //witnesscircuit witness.Witness

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, cname)

	pk, vk, _ := groth16.Setup(ccs)

	tproofstart := time.Now()
	fmt.Println("Starting Proving ")

	proof, errproof := groth16.Prove(ccs, pk, witnesscircuit)
	fmt.Println("Error Proving ", errproof)
	fmt.Fprintln(file, "Error in Proving ", circuitname, ": ", errproof)

	tproofend := time.Now()
	timetoprove := tproofend.Sub(tproofstart)

	fmt.Fprintln(file, "Error in Proving ", circuitname, ": ", errproof)
	publicWitness, _ := witnesscircuit.Public()
	tverifystart := time.Now()
	errverify := groth16.Verify(proof, vk, publicWitness)
	tverifyend := time.Now()
	timetoverify := tverifyend.Sub(tverifystart)
	fmt.Fprintln(file, "Error in Verifying ", circuitname, ": ", errverify)

	var buffer bytes.Buffer
	encoder := gob.NewEncoder(&buffer)
	if err := encoder.Encode(proof); err != nil {
		fmt.Fprintln(file, "Error encoding proof ", circuitname, ": ", err)
	}

	// Calculate the size of the byte slice, which represents the proof
	proofSize := len(buffer.Bytes())
	return timetoprove, timetoverify, proofSize
}

func grothproveverify_nofile(cname frontend.Circuit, assignment frontend.Circuit, circuitname string) (time.Duration, time.Duration, int) {
	witnesscircuit, _ := frontend.NewWitness(assignment, ecc.BN254.ScalarField()) //witnesscircuit witness.Witness

	ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, cname)

	pk, vk, _ := groth16.Setup(ccs)

	tproofstart := time.Now()
	fmt.Println("Starting Proving ")

	proof, errproof := groth16.Prove(ccs, pk, witnesscircuit)
	fmt.Println("Error in Proving ", circuitname, ": ", errproof)

	tproofend := time.Now()
	timetoprove := tproofend.Sub(tproofstart)

	fmt.Println("Error in Proving ", circuitname, ": ", errproof)
	publicWitness, _ := witnesscircuit.Public()
	tverifystart := time.Now()
	errverify := groth16.Verify(proof, vk, publicWitness)
	tverifyend := time.Now()
	timetoverify := tverifyend.Sub(tverifystart)
	fmt.Println("Error in Verifying ", circuitname, ": ", errverify)

	var buffer bytes.Buffer
	encoder := gob.NewEncoder(&buffer)
	if err := encoder.Encode(proof); err != nil {
		fmt.Println("Error encoding proof ", circuitname, ": ", err)
	}

	// Calculate the size of the byte slice, which represents the proof
	proofSize := len(buffer.Bytes())
	return timetoprove, timetoverify, proofSize
}

func find_average_w_std(numbers []int) (float64, float64, float64) {
	var sum int
	count := len(numbers)
	for _, num := range numbers {
		sum += num
	}

	average := float64(sum) / float64(len(numbers))

	var sumSquaredDifferences float64
	for _, num := range numbers {
		difference := float64(num) - average
		sumSquaredDifferences += difference * difference
	}

	// Calculate the variance and standard deviation
	variance := sumSquaredDifferences / float64(count)
	standardDeviation := math.Sqrt(variance)

	return average, float64(sum), standardDeviation
}

func convertToFloat64Slice(interfaceSlice []interface{}) []float64 {
	floatSlice := make([]float64, len(interfaceSlice))

	for i, v := range interfaceSlice {
		// Perform type assertion to convert each element to float64
		floatSlice[i] = v.(float64)
	}

	return floatSlice
}
func convertToFloat64Slicewithrounding(interfaceSlice []interface{}) []float64 {
	floatSlice := make([]float64, len(interfaceSlice))

	for i, v := range interfaceSlice {
		// Perform type assertion to convert each element to float64
		floatSlice[i] = math.Round(v.(float64))
	}

	return floatSlice
}
func equalVecs(vec1, vec2 *mat.VecDense) bool {
	// Check dimensions first
	rows1, _ := vec1.Dims()
	rows2, _ := vec2.Dims()

	if rows1 != rows2 {
		log.Fatal("Vectors have different dimensions")
	}

	// Check element-wise equality
	for i := 0; i < rows1; i++ {
		if vec1.AtVec(i) != vec2.AtVec(i) {
			return false
		}
	}

	return true
}

func AbsVecDense_withsensattremoval(original *mat.VecDense) *mat.VecDense {
	rows, _ := original.Dims()

	// Create a new vector with the same size
	absVec := mat.NewVecDense(rows-1, nil)

	// Apply the absolute value to each element
	for i := 0; i < rows-1; i++ {

		value := original.AtVec(i + 1)
		absValue := math.Abs(value)
		absVec.SetVec(i, absValue)

	}
	return absVec
}

func find_point_on_facet(file *os.File, f facet_general, facet_on_point_map map[string][][][]interface{}, hiddenLayerSize []int, layersizes []int, fullvalidinddict map[int]int) (*mat.VecDense, error) {

	var pt []float64
	//var b float64
	fulllayeredarray := codetolayeredarray(f.polywhichcreated, hiddenLayerSize)
	actual_size_str_code := actual_layersize_code(fulllayeredarray, layersizes)

	if f.fType == "decision" {
		/*a = facet_on_point_map[f.polywhichcreated][1][0][0].([]float64)
		b = facet_on_point_map[f.polywhichcreated][1][0][1].(float64)*/
		if facet_on_point_map[actual_size_str_code] != nil {
			if len(facet_on_point_map[actual_size_str_code][1]) != 0 {
				if reflect.TypeOf(facet_on_point_map[actual_size_str_code][1][0][2]).Kind() != reflect.Float64 {
					pt = convertToFloat64Slice(facet_on_point_map[actual_size_str_code][1][0][2].([]interface{}))
				}
			}
		}

	} else {
		list_ind := -1
		if facet_on_point_map[actual_size_str_code] != nil {
			normal_facet_list := facet_on_point_map[actual_size_str_code][0]
			for i := 0; i < len(normal_facet_list); i++ {
				avecfromlist := mat.NewVecDense(f.a.Len(), convertToFloat64Slicewithrounding(normal_facet_list[i][0].([]interface{})))
				floatb, _ := strconv.ParseFloat(normal_facet_list[i][1].(string), 64)
				if equalVecs(avecfromlist, f.a) && floatb == f.b {
					list_ind = i
					break
				}
			}
			if list_ind != -1 {
				if normal_facet_list[list_ind][2] != float64(-1) {
					//fmt.Println("printing type: ", reflect.TypeOf(normal_facet_list[list_ind][2]), normal_facet_list[list_ind][2])
					pttofeed := normal_facet_list[list_ind][2].([]interface{})
					pt = convertToFloat64Slice(pttofeed)
				}

			}
		}
		/*a = normal_facet_list[tight_list_ind][0].([]float64)
		b = normal_facet_list[tight_list_ind][1].(float64)*/

	}
	x := mat.NewVecDense(f.a.Len(), pt)
	fmt.Fprintln(file, "Finding point for ", f.a, f.b)
	fmt.Fprintln(file, "The found point is ", pt)
	var err error
	if x == nil {
		err = errors.New("Couldn't find point for facet")
		log.Printf("Failed to solve: %v", err)
	}
	return x, err
}

func find_diff(LA *mat.Dense, LB *mat.VecDense, Lpt *mat.VecDense) {
	A := mat.DenseCopyOf(LA)
	B := mat.VecDenseCopyOf(LB)
	pt := mat.VecDenseCopyOf(Lpt)
	new_mat := mat.NewVecDense(B.Len(), nil)
	pt.ScaleVec(math.Pow(roundingcoeff, roundingpower), pt)
	B.ScaleVec(math.Pow(roundingcoeff, roundingpower), B)
	new_mat.MulVec(A, pt)
	new_mat.AddVec(new_mat, B)
	diff := new_mat.AtVec(0) - new_mat.AtVec(1)
	fmt.Println("Difference :", diff)
}

//func Prove_Verify(t *testing.T, sens int, model_str string, file *os.File, dirPath string, limits_var limits) map[string]interface{} -- alternate signature of the function

func Prove_Verify(t *testing.T, sens int, model_str string, file *os.File, dirPath string, limits_var limits) float64 {

	var weightsBiases weights_general
	var allweights []*mat.Dense
	var allbiases []*mat.VecDense
	var initActCodePy code
	var layersizes layer_sizes_dict
	var inputpt input
	var initpoly polytope_general
	var runningpoly polytope_general
	var code_pt_list code_pt_dict
	var facetpt_list facetpt
	var radius_output float64
	var facet_pt_error error

	field_size := ecc.BN254.ScalarField()
	field_size_minusone := new(big.Int).Sub(field_size, big.NewInt(1))
	field_mid := new(big.Int).Div(field_size_minusone, big.NewInt(2))

	fnameWeights := fmt.Sprintf("%s/original_weights_unrounded_unscaled_%s_%d.json", dirPath, model_str, sens)
	fnameinitactcode := fmt.Sprintf("%s/initpolytope_%s_%d.json", dirPath, model_str, sens)
	fnameinput := fmt.Sprintf("%s/inputpoint_%s_%d.json", dirPath, model_str, sens)
	fnamelayersizes := fmt.Sprintf("%s/layer_sizes_%s_%d.json", dirPath, model_str, sens)
	fnamecodepts := fmt.Sprintf("%s/point_polytope_dict_%s_%d.json", dirPath, model_str, sens)
	fnamefacetpts := fmt.Sprintf("%s/with_pt_per_poly_dict_%s_%d.json", dirPath, model_str, sens)

	count_facets := 0
	init_facets := 0

	vneighborprooftimes := []time.Duration{}
	vneighborverifytimes := []time.Duration{}
	vneighborproofsizes := []int{}

	//hint.Register(quoremhint_QuoRem)

	readcodeptdict(fnamecodepts, &code_pt_list)
	readfile_initactivation_code(fnameinitactcode, &initActCodePy)
	readfile_weights(fnameWeights, &weightsBiases)
	readfile_layer_sizes(fnamelayersizes, &layersizes)
	readfile_input(fnameinput, &inputpt)
	readfacetptdict(fnamefacetpts, &facetpt_list)

	polytraversedpython := mapset.NewSet[string]()

	inputSize := len(inputpt.InputPoint)
	fx, ix := round_vecdense(inputpt.InputPoint)
	fmt.Fprintln(file, "input point: ", ix)
	x := mat.NewVecDense(inputSize, fx)

	hiddenLayerSize := layersizes.LayerSizes

	allweights, allbiases = convert_to_matrix(weightsBiases, hiddenLayerSize, inputSize)
	allweightsfull, allbiasesfull := convert_to_matrix(weightsBiases, append(hiddenLayerSize, outlogits), inputSize)

	hiddenLayerSize = []int{inputsizeconst, inputsizeconst}
	totalNeurons := totalneurons(hiddenLayerSize) //found using padded size
	fullhiddenLayerSize := append(hiddenLayerSize, inputsizeconst)
	totalNeuronsfull := totalneurons(fullhiddenLayerSize)
	fmt.Fprintln(file, "fullhiddenlayersize: ", fullhiddenLayerSize, hiddenLayerSize)
	rand.Seed(time.Now().UnixNano())
	_, rm := round_pad_allweights(allweights)
	allweights = rm
	_, rbm := round_pad_biases(allbiases)
	allbiases = rbm

	fullrm := full_round_pad_allweights(allweightsfull) //just take the previous allweights and append to that the last two of allweightsfull
	allweightsfull = fullrm
	fullrbm := full_round_pad_biases(allbiasesfull)
	allbiasesfull = fullrbm

	_, fullinitActCodeGoarray := findactivationcode(allweightsfull, allbiasesfull, fullhiddenLayerSize, x)
	initActCodeGo, initActCodeGoarray := findactivationcode(allweights, allbiases, hiddenLayerSize, x)

	fmt.Fprintln(file, "init codes, go and python: ", initActCodeGo, initActCodePy)
	initpoly.A, initpoly.b = getpolytopefromcode(initActCodeGoarray, allweights, allbiases, hiddenLayerSize, totalNeurons, inputSize)
	initpoly.code = flatten_code_array(initActCodeGoarray, hiddenLayerSize) //initActCodeGoarray
	initpoly.fullcode = flatten_code_array(fullinitActCodeGoarray, fullhiddenLayerSize)
	fmt.Fprintln(file, "printing ", initActCodeGo[:totalNeurons-hiddenLayerSize[len(hiddenLayerSize)-1]] == initActCodePy.ActivationCode)
	fmt.Println("Verify activation code init starting")

	var verifyinitact verifyactivationcode
	assignment_verifyinitact := verifyactivationcode{
		Callweights:          convert_allweights_frontendvariable(allweights),
		Cx:                   convert_intarray_frontendvariable(ix),
		Chidden_layer_size:   [numlayersconst]frontend.Variable{inputsizeconst, inputsizeconst}, //change with size
		Callbiases:           convert_allbiases_frontendvariable(allbiases),
		Actcodearray:         convert_arrofarr_frontendvariable(initActCodeGoarray),
		FieldSizeminusone:    frontend.Variable(field_size_minusone),
		FieldSizeminusoneby2: frontend.Variable(field_mid)}

	initactprovetime, initactverifytime, initactproofsize := grothproveverify(&verifyinitact, &assignment_verifyinitact, "initactcode", file)
	fmt.Println(initactprovetime, initactverifytime, initactproofsize)
	fmt.Println("Verify activation code init ending")

	fmt.Println("Verify polytope init starting")

	var verifyinitpoly verifypolytope
	assignment_verifyinitpoly := verifypolytope{
		Callweights:   convert_allweights_frontendvariable(allweights),
		Callbiases:    convert_allbiases_frontendvariable(allbiases),
		Cactcodearray: convert_arrofarr_frontendvariable(initActCodeGoarray),
		Polyb:         convert_polyb_to_frontend(initpoly.b),
		PolyA:         convert_polyA_to_frontend(initpoly.A),
	}
	initpolyprovetime, initpolyverifytime, initpolyproofsize := grothproveverify(&verifyinitpoly, &assignment_verifyinitpoly, "verifypoly init", file)
	fmt.Println(initpolyprovetime, initpolyverifytime, initpolyproofsize)
	fmt.Println("Verify polytope init end")

	fullvalidinds := find_full_valid_indices(layersizes.LayerSizes)
	fmt.Fprintln(file, "validinds: ", fullvalidinds)
	fullvalidinddict := make(map[int]int)
	for i := 0; i < len(fullvalidinds); i++ {
		fullvalidinddict[fullvalidinds[i]] = i
	}
	fmt.Fprintln(file, "fullvalidinddict: ", fullvalidinddict)

	validinds := fullvalidinds[:len(fullvalidinds)-outlogits]
	facetPotPq := make(PriorityQueue, 1)

	var initcodeptlist codept

	_, initcodeptlist.Code = findsmallcode(validinds, codetoflattenedarray(initActCodeGo))
	initcodeptlist.Pt = inputpt.InputPoint
	code_pt_list.PointPolytopeList = append(code_pt_list.PointPolytopeList, initcodeptlist)

	for i := 0; i < len(code_pt_list.PointPolytopeList); i++ {
		polytraversedpython.Add(code_pt_list.PointPolytopeList[i].Code)
	}
	facet_with_pt_dict := make(map[string][][][]interface{})
	for _, poly_in_list := range facetpt_list.PerPolyListWithPt {
		normalFacets := poly_in_list.NormalFacets
		decisionFacets := poly_in_list.DecisionFacets
		facet_with_pt_dict[poly_in_list.PolytopeConfig] = [][][]interface{}{normalFacets, decisionFacets}
	}

	//numberofseenfacets := len(facet_with_pt_dict) * totalNeurons

	runningpoly.A = initpoly.A
	runningpoly.b = initpoly.b
	runningpoly.code = initpoly.code
	runningpoly.fullcode = initpoly.fullcode

	seenPolytopes_actualcode := []string{}
	seenPolytopes := mapset.NewSet[string]()

	fulllayeredarray := codetolayeredarray(initpoly.code, hiddenLayerSize)
	actual_size_str_code := actual_layersize_code(fulllayeredarray, layersizes.LayerSizes)

	fmt.Fprintln(file, "starting polytope: ", initpoly.code)
	fmt.Fprintln(file, "Initial Polytope description A: ", initpoly.A)
	fmt.Fprintln(file, "Initial Polytope description b: ", initpoly.b)

	fmt.Fprintln(file, "Seen poly set : ", seenPolytopes)
	fmt.Fprintln(file, "New addition to seen polytopes: ", actual_size_str_code)
	fmt.Fprintln(file, "Seen polytopes actual code: ", seenPolytopes_actualcode)
	rejected_inds_dict := make(map[string][]int)

	fullcodetotest := codetolayeredarray(initpoly.fullcode, fullhiddenLayerSize)
	fullA, fullb := getpolytopefromcode(fullcodetotest, allweightsfull, allbiasesfull, fullhiddenLayerSize, totalNeuronsfull, inputSize)
	linearmapa, linearmapb, logits, true_label := get_linear_map(fullcodetotest, allweightsfull, allbiasesfull, fullhiddenLayerSize, totalNeuronsfull, inputSize, fx)
	fmt.Fprintln(file, "Init total facets: ", len(validinds))
	first_time_facetpq := 1

	for j := 0; j < len(validinds); j++ {

		var tempfacet facet_general
		loc := validinds[j]
		fmt.Fprintln(file, "full valid inds: ", validinds)

		if !seenPolytopes.Contains(flipBitAtIndex(initpoly.code, loc)) {
			fmt.Fprintln(file, "In init for index: ", j)
			tempa := initpoly.A.RawRowView(loc)
			tempfacet.a = mat.NewVecDense(len(tempa), tempa)
			tempfacet.b = initpoly.b.AtVec(loc)
			tempfacet.polywhichcreated = initpoly.code
			tempfacet.polywhichcreatedfull = initpoly.fullcode
			tempfacet.tight = loc
			tempfacet.linearmapa = linearmapa
			tempfacet.linearmapb = linearmapb
			proj, _, _ := projection_general(tempfacet, x)
			if math.IsInf(proj, 1) || math.IsInf(proj, -1) || math.IsNaN(proj) { //
				fmt.Fprintln(file, "In init if nan for index ", j)
				continue
			}
			if first_time_facetpq == 1 {
				facetPotPq[0] = &item{
					value:    tempfacet,
					priority: -1 * proj,
					index:    loc,
				}
				heap.Init(&facetPotPq)
				first_time_facetpq = -1
			} else {
				heapToAdd := &item{
					value:    tempfacet,
					priority: -1 * proj,
				}
				heap.Push(&facetPotPq, heapToAdd)
			}
			/*facetPotPq[j] = &item{
				value:    tempfacet,
				priority: -1 * proj,
				index:    loc,
			}*/
			fmt.Fprintln(file, "Added element to facetpotpq ", j)

			projection_general_diff_check(tempfacet, x)
			a_abs := AbsVecDense_withsensattremoval(tempfacet.a)
			var vproj verifyprojection
			assignment_vproj := verifyprojection{
				Ca:                convert_vecdense_to_frontend(tempfacet.a),
				Ca_abs:            convert_vecdense_to_frontend_smallsize(a_abs),
				Cb_extra_scaled:   frontend.Variable(int(math.Round(tempfacet.b * math.Pow(roundingcoeff, roundingpower)))),
				Cx0:               convert_intarray_frontendvariable(ix),
				Cprojsq:           frontend.Variable(int(math.Round(proj * proj * math.Pow(roundingcoeff, roundingpower) * math.Pow(roundingcoeff, roundingpower)))),
				Limitsq_eq:        frontend.Variable(int(limits_var.ProjectionNormalInit)),
				CFieldminusoneby2: frontend.Variable(field_mid)}

			vprojprovetime, vprojverifytime, projproofsize := grothproveverify(&vproj, &assignment_vproj, "projection_normal_init", file)
			fmt.Println(vprojprovetime, vprojverifytime, projproofsize)
			count_facets += 1
			init_facets += 1
			fmt.Fprintln(file, "Init normal facet, distance: ", -1*proj, tempfacet.a, tempfacet.b, tempfacet.polywhichcreated)
		} else {
			rejected_inds_dict[actual_size_str_code] = append(rejected_inds_dict[actual_size_str_code], fullvalidinddict[loc])
			continue
		}
	}
	seenPolytopes.Add(initpoly.code)
	seenPolytopes_actualcode = append(seenPolytopes_actualcode, actual_size_str_code)
	fmt.Fprintln(file, "Init facetpq len: ", facetPotPq.Len())
	//heap.Init(&facetPotPq)
	fmt.Fprintln(file, "Init facetpq len: ", facetPotPq.Len())
	new_decision_facets := make_adversarial_constraints(linearmapa, linearmapb, true_label, initpoly)

	new_decision_facets[0].dec_pt, facet_pt_error = find_point_on_facet(file, new_decision_facets[0], facet_with_pt_dict, hiddenLayerSize, layersizes.LayerSizes, fullvalidinddict)
	fmt.Println("Outside error")
	if facet_pt_error == nil {

		new_decision_facets[0].linearmapa = linearmapa
		new_decision_facets[0].linearmapb = linearmapb

		pt := new_decision_facets[0].dec_pt
		fmt.Println(pt)
		result := mat.NewVecDense(linearmapb.Len(), nil)
		result.MulVec(linearmapa, pt)
		result.AddVec(result, linearmapb)
		fmt.Println(result)

		fmt.Fprintln(file, "fullA, fullb: ", fullA, fullb)
		fmt.Fprintln(file, "Init poly decision facets A & b: ", new_decision_facets[0].a, new_decision_facets[0].b)
		fmt.Fprintln(file, "Linear mapa, linearmap b: ", linearmapa, linearmapb)
		fmt.Fprintln(file, "logits, truelabel : ", logits, true_label)
		fmt.Println("new_decision_facets init : ", new_decision_facets[0].a, new_decision_facets[0].b)

		var makeadvconstscircuit VerifyMakeAdvConstraints
		assignmentMakeAdvConst := VerifyMakeAdvConstraints{AdvA: convert_vecdense_to_frontend(new_decision_facets[0].a),
			AdvB:          frontend.Variable(int(math.Round(new_decision_facets[0].b))),
			Truelabela:    convert_vecdense_to_frontend(mat.NewVecDense(inputsizeconst, linearmapa.RawRowView(true_label))),
			NotTruelabela: convert_vecdense_to_frontend(mat.NewVecDense(inputsizeconst, linearmapa.RawRowView(1-true_label))),
			Truelabelb:    frontend.Variable(int(math.Round(linearmapb.AtVec(true_label)))),
			NotTruelabelb: frontend.Variable(int(math.Round(linearmapb.AtVec(1 - true_label))))}

		prooftimemakeadv, verifytimemakeadv, makeadvproofsize := grothproveverify(&makeadvconstscircuit, &assignmentMakeAdvConst, "makeadv", file)
		fmt.Println(prooftimemakeadv, verifytimemakeadv, makeadvproofsize)
		for i := 0; i < len(new_decision_facets); i++ {
			new_decision_facet := new_decision_facets[i]
			proj, _, _ := projection_general(new_decision_facet, x)
			if math.IsInf(proj, 1) || math.IsInf(proj, -1) || math.IsNaN(proj) { //math.IsInf(proj, 1) || math.IsInf(proj, -1) ||
				continue
			}

			heapToAdd := &item{
				value:    new_decision_facet,
				priority: -1 * proj,
			}

			projection_general_diff_check(new_decision_facet, x)
			a_abs := AbsVecDense_withsensattremoval(new_decision_facet.a)

			fmt.Println("Decision Init facet started")

			var vproj verifyprojection
			assignment_vproj := verifyprojection{
				Ca:                convert_vecdense_to_frontend(new_decision_facet.a),
				Ca_abs:            convert_vecdense_to_frontend_smallsize(a_abs),
				Cb_extra_scaled:   frontend.Variable(int(math.Round(new_decision_facet.b * math.Pow(roundingcoeff, roundingpower)))),
				Cx0:               convert_intarray_frontendvariable(ix),
				Cprojsq:           frontend.Variable(int(math.Round(proj * proj * math.Pow(roundingcoeff, roundingpower) * math.Pow(roundingcoeff, roundingpower)))),
				Limitsq_eq:        frontend.Variable(int(limits_var.ProjectionDecisionInit)),
				CFieldminusoneby2: frontend.Variable(field_mid)}

			vprojprovetime, vprojverifytime, projproofsize := grothproveverify(&vproj, &assignment_vproj, "projection_decision_init", file)
			fmt.Println(vprojprovetime, vprojverifytime, projproofsize)
			fmt.Println("Decision Init facet Done")
			heap.Push(&facetPotPq, heapToAdd)

			count_facets += 1
			fmt.Fprintln(file, "Init decision facet, distance: ", -1*proj, new_decision_facet.a, new_decision_facet.b, new_decision_facet.polywhichcreated)
		}
	}

	prediction_x, logitsx, penult := inference(allweightsfull, allbiasesfull, append(hiddenLayerSize, inputsizeconst), mat.NewVecDense(len(ix), fx))
	fmt.Fprintln(file, "x prediction and logits: ", prediction_x, logitsx)
	fmt.Println("x prediction and logits: ", prediction_x, logitsx)
	fmt.Println("penult: ", penult)
	var vinf verifyinference
	assignment_verifyinference := verifyinference{
		Callweightsfull: convert_allweightsfull_frontendvariable(allweightsfull),
		Callbiasesfull:  convert_allbiasesfull_frontendvariable(allbiasesfull),
		Cfout:           frontend.Variable(prediction_x),
		Cx:              convert_intarray_frontendvariable(ix),
	}

	infprooftime, infverifytime, infproofsize := grothproveverify(&vinf, &assignment_verifyinference, "inference", file)
	fmt.Println(infprooftime, infverifytime, infproofsize)
	/*var vinfsmall verifyinference_small
	assignment_verifyinferencesmall := verifyinference_small{
		CWeightslast:      convert_allweightsfull_frontendvariable_lastlayer(allweightsfull[numlayersconst]),
		CBiaseslast:       convert_vecdense_to_frontend_outlogits(allbiasesfull[numlayersconst]),
		Cpenult:           convert_vecdense_to_frontend_penult(penult),
		Clargerlogitind:   generateIntSlice(prediction_x),
		CFieldminusoneby2: frontend.Variable(field_mid)}

	infprooftime, infverifytime, infproofsize := grothproveverify(&vinfsmall, &assignment_verifyinferencesmall, "small_inference", file)*/

	for len(facetPotPq) > 0 {
		fmt.Fprintln(file, "Length of facetpotpq using .Len(): ", facetPotPq.Len())
		fmt.Fprintln(file, "Length using len : ", len(facetPotPq))
		fmt.Fprintln(file, "Heap at entry: ")
		printpq(facetPotPq, fullvalidinddict, hiddenLayerSize, layersizes.LayerSizes, file)
		fmt.Fprintln(file, "Seen polytopes: ", seenPolytopes)
		fmt.Fprintln(file, "Actual Size Seen polytopes: ", seenPolytopes_actualcode)
		poppedItem := heap.Pop(&facetPotPq).(*item)
		fmt.Fprintln(file, "popped item: ", poppedItem.priority, actual_layersize_code(codetolayeredarray(poppedItem.value.polywhichcreated, hiddenLayerSize), layersizes.LayerSizes), fullvalidinddict[poppedItem.value.tight])
		fmt.Fprintln(file, "heap after popping: ")
		printpq(facetPotPq, fullvalidinddict, hiddenLayerSize, layersizes.LayerSizes, file)
		fmt.Println("after popping heap size using .Len and len: ", facetPotPq.Len(), len(facetPotPq))
		current_pq_list := []float64{}
		for p := 0; p < facetPotPq.Len(); p++ {
			current_pq_list = append(current_pq_list, facetPotPq[p].priority*-1)

		}
		//sort.Float64s(current_pq_list)
		current_list_len := len(current_pq_list)
		fmt.Fprintln(file, "Current list len: ", current_list_len)
		fmt.Fprintln(file, "Current pq list: ", current_pq_list)
		for p := current_list_len; p < maxheapsize; p++ {
			current_pq_list = append(current_pq_list, (poppedItem.priority*-1)+1) //p < maxheapsize  current_pq_list[current_list_len-1]+1
		}

		fmt.Fprintln(file, "After adding maxheap Current pq list: ", current_pq_list)

		scalingfactor := float64(5)
		//convert_heap_to_frontend_scaling(current_pq_list, scalingfactor)

		var verifymin VerifyHeapPop
		assignment_verifymin := VerifyHeapPop{
			List:    convert_heap_to_frontend_scaling(current_pq_list, scalingfactor),
			MinItem: frontend.Variable(int(math.Round(poppedItem.priority * -1 * math.Pow(roundingcoeff, roundingpower*scalingfactor))))} //scaling factor here should be same as in the convert_heap function

		minprooftime, minverifytime, minproofsize := grothproveverify(&verifymin, &assignment_verifymin, "heap_pop", file)
		fmt.Println(minprooftime, minverifytime, minproofsize)
		if CheckDecision(poppedItem.value) {
			result_facet := poppedItem.value
			fmt.Println("Decision check")

			A, B := getpolytopefromcode(codetolayeredarray(poppedItem.value.polywhichcreated, hiddenLayerSize), allweights, allbiases, hiddenLayerSize, totalNeurons, inputSize)
			fmt.Println("pt: ", result_facet.dec_pt, A, B)

			/*sign_vector, sign_flag := create_sign_vector(t, A, B, result_facet.dec_pt)
			if sign_flag == -1 {
				fmt.Println("In decision Sign vector not all zeroes: ", sign_vector)
				continue
			}*/

			var verifypointonfacet VerifyPointOnFacet
			assignment_verifypointonfacet := VerifyPointOnFacet{
				Pt:               convert_vecdense_to_frontend_scaling(result_facet.dec_pt),
				Facet_eq_A:       convert_vecdense_to_frontend(result_facet.a),
				Facet_eq_B:       frontend.Variable(int(result_facet.b * math.Pow(roundingcoeff, roundingpower))),
				Limitsq_eq:       frontend.Variable(int(limits_var.PointonfacetcheckDecision)),
				Facet_ineq_A:     convert_polyA_to_frontend(A),
				Facet_ineq_B:     convert_polyb_to_frontend_extra_scaling(B),
				Fieldminusoneby2: frontend.Variable(field_mid)}

			pointonfacetprooftime, pointonfacetverifytime, pointonfacetproofsize := grothproveverify(&verifypointonfacet, &assignment_verifypointonfacet, "pointonfacet_decision", file)
			fmt.Println(pointonfacetprooftime, pointonfacetverifytime, pointonfacetproofsize)

			find_diff(result_facet.linearmapa, result_facet.linearmapb, result_facet.dec_pt)

			var verifydecision VerifyDecisionFacetCheck
			assignment_verifydecision := VerifyDecisionFacetCheck{
				Pt:               convert_vecdense_to_frontend_scaling(result_facet.dec_pt),
				LinearMapA0:      convert_vecdense_to_frontend(mat.NewVecDense(inputsizeconst, result_facet.linearmapa.RawRowView(0))),
				LinearMapA1:      convert_vecdense_to_frontend(mat.NewVecDense(inputsizeconst, result_facet.linearmapa.RawRowView(1))),
				LinearMapB0:      frontend.Variable(int(math.Round(result_facet.linearmapb.AtVec(0) * math.Pow(roundingcoeff, roundingpower)))),
				LinearMapB1:      frontend.Variable(int(math.Round(result_facet.linearmapb.AtVec(1) * math.Pow(roundingcoeff, roundingpower)))),
				Limit:            frontend.Variable(int(limits_var.FacetcheckDecision)),
				Fieldminusoneby2: frontend.Variable(field_mid)}

			decprooftime, decverifytime, decproofsize := grothproveverify(&verifydecision, &assignment_verifydecision, "decisioncheck", file)
			fmt.Println(decprooftime, decverifytime, decproofsize)
			radius_output = poppedItem.priority

			break
		} else {

			current_facet := poppedItem.value
			current_facet.dec_pt, facet_pt_error = find_point_on_facet(file, poppedItem.value, facet_with_pt_dict, hiddenLayerSize, layersizes.LayerSizes, fullvalidinddict)

			A, B := getpolytopefromcode(codetolayeredarray(poppedItem.value.polywhichcreated, hiddenLayerSize), allweights, allbiases, hiddenLayerSize, totalNeurons, inputSize)
			fmt.Println("pt: ", current_facet.dec_pt)

			/*sign_vector, sign_flag := create_sign_vector(t, A, B, current_facet.dec_pt)
			if sign_flag == -1 {
				fmt.Println("Sign vector not all zeroes: ", sign_vector)
				continue
			}*/

			fmt.Println("B: ", B)
			fmt.Println("A:", A)

			var verifypointonfacet VerifyPointOnFacet
			assignment_verifypointonfacet := VerifyPointOnFacet{
				Pt:               convert_vecdense_to_frontend_scaling(current_facet.dec_pt), //convert_vecdense_to_frontend_no_round(current_facet.dec_pt),
				Facet_eq_A:       convert_vecdense_to_frontend(current_facet.a),
				Facet_eq_B:       frontend.Variable(int(current_facet.b * math.Pow(roundingcoeff, roundingpower))),
				Limitsq_eq:       frontend.Variable(int(limits_var.PointonfacetcheckNormal)),
				Facet_ineq_A:     convert_polyA_to_frontend(A),
				Facet_ineq_B:     convert_polyb_to_frontend_extra_scaling(B),
				Fieldminusoneby2: frontend.Variable(field_mid)}

			pointonfacetprooftime, pointonfacetverifytime, pointonfacetproofsize := grothproveverify(&verifypointonfacet, &assignment_verifypointonfacet, "pointonfacet_normal", file)
			fmt.Println(pointonfacetprooftime, pointonfacetverifytime, pointonfacetproofsize)
			fmt.Println("Normal Facet diff")
			find_diff(current_facet.linearmapa, current_facet.linearmapb, current_facet.dec_pt)

			var verifynormal VerifyNormalFacetCheck
			assignment_verifynormal := VerifyNormalFacetCheck{
				Pt:          convert_vecdense_to_frontend_scaling(current_facet.dec_pt),
				LinearMapA0: convert_vecdense_to_frontend(mat.NewVecDense(inputsizeconst, current_facet.linearmapa.RawRowView(0))),
				LinearMapA1: convert_vecdense_to_frontend(mat.NewVecDense(inputsizeconst, current_facet.linearmapa.RawRowView(1))),
				LinearMapB0: frontend.Variable(int(math.Round(current_facet.linearmapb.AtVec(0) * math.Pow(roundingcoeff, roundingpower)))),
				LinearMapB1: frontend.Variable(int(math.Round(current_facet.linearmapb.AtVec(1) * math.Pow(roundingcoeff, roundingpower)))),
				Limit:       frontend.Variable(int(limits_var.FacetcheckNormal))}

			normalprooftime, normalverifytime, normalproofsize := grothproveverify(&verifynormal, &assignment_verifynormal, "normalcheck", file)
			fmt.Println(normalprooftime, normalverifytime, normalproofsize)

			var neighborpoly polytope_general

			new_poly_code := findNeighborPolytope(poppedItem.value)
			new_poly_code_full := findNeighborPolytopefull(poppedItem.value)
			fmt.Fprintln(file, "New poly code: ", new_poly_code)
			fmt.Fprintln(file, "New poly code full: ", new_poly_code_full)
			neighborpoly.code = new_poly_code
			neighborpoly.fullcode = new_poly_code_full
			neighborpoly.A, neighborpoly.b = getpolytopefromcode(codetolayeredarray(new_poly_code, hiddenLayerSize), allweights, allbiases, hiddenLayerSize, totalNeurons, inputSize)
			//if polytraversedpython.Contains(new_poly_code) Do you need this?

			oldcode := poppedItem.value.polywhichcreated
			oldA, oldb := getpolytopefromcode(codetolayeredarray(oldcode, hiddenLayerSize), allweights, allbiases, hiddenLayerSize, totalNeurons, inputSize)
			fmt.Fprintln(file, "Olda, oldb: ", oldA, oldb)

			fulllayeredarray = codetolayeredarray(new_poly_code, hiddenLayerSize)
			actual_size_str_code = actual_layersize_code(fulllayeredarray, layersizes.LayerSizes)

			fmt.Fprintln(file, "Seen polytopes: ", seenPolytopes)
			fmt.Fprintln(file, "Actual Size Seen polytopes: ", seenPolytopes_actualcode)

			fullcodetotest = codetolayeredarray(neighborpoly.fullcode, fullhiddenLayerSize)
			fullA, fullb = getpolytopefromcode(fullcodetotest, allweightsfull, allbiasesfull, fullhiddenLayerSize, totalNeuronsfull, inputSize)

			if !seenPolytopes.Contains(new_poly_code) && polytraversedpython.Contains(actual_size_str_code) {

				vneighborproofsizes, vneighborprooftimes, vneighborverifytimes = verifyNeighbor(file, vneighborproofsizes, vneighborprooftimes, vneighborverifytimes, code_pt_list, new_poly_code, poppedItem.value.polywhichcreated, allweights, allbiases, hiddenLayerSize, t, oldA, oldb, neighborpoly.A, neighborpoly.b, poppedItem.value.tight, layersizes.LayerSizes)

				linearmapa, linearmapb, logits, true_label = get_linear_map(fullcodetotest, allweightsfull, allbiasesfull, fullhiddenLayerSize, totalNeuronsfull, inputSize, fx)
				fmt.Fprintln(file, "fullA, fullb: ", fullA, fullb)
				fmt.Fprintln(file, "lastlayera, lastlayerb, true_label: ", linearmapa, linearmapb, true_label)

				new_decision_facets = make_adversarial_constraints(linearmapa, linearmapb, true_label, neighborpoly)
				new_decision_facets[0].dec_pt, facet_pt_error = find_point_on_facet(file, new_decision_facets[0], facet_with_pt_dict, hiddenLayerSize, layersizes.LayerSizes, fullvalidinddict)
				if facet_pt_error == nil {

					new_decision_facets[0].linearmapa = linearmapa
					new_decision_facets[0].linearmapb = linearmapb
					fmt.Println("new_decision_facets in loop: ", new_decision_facets[0].a, new_decision_facets[0].b)
					fmt.Fprintln(file, "new decision facets: ", new_decision_facets[0].a, new_decision_facets[0].b, len(new_decision_facets))

					var makeAdvConstcircuit2 VerifyMakeAdvConstraints
					assignment_makeadv2 := VerifyMakeAdvConstraints{AdvA: convert_vecdense_to_frontend(new_decision_facets[0].a),
						AdvB:          frontend.Variable(int(math.Round(new_decision_facets[0].b))),
						Truelabela:    convert_vecdense_to_frontend(mat.NewVecDense(inputsizeconst, linearmapa.RawRowView(true_label))),
						NotTruelabela: convert_vecdense_to_frontend(mat.NewVecDense(inputsizeconst, linearmapa.RawRowView(1-true_label))),
						Truelabelb:    frontend.Variable(int(math.Round(linearmapb.AtVec(true_label)))),
						NotTruelabelb: frontend.Variable(int(math.Round(linearmapb.AtVec(1 - true_label))))}
					makeadvprooftime, makeadvverifytime, makeadvproofsize := grothproveverify(&makeAdvConstcircuit2, &assignment_makeadv2, "makeadv", file)
					fmt.Println(makeadvprooftime, makeadvverifytime, makeadvproofsize)

					for i := 0; i < len(new_decision_facets); i++ {
						new_decision_facet := new_decision_facets[i]
						proj, _, _ := projection_general(new_decision_facet, x)
						if math.IsInf(proj, 1) || math.IsInf(proj, -1) || math.IsNaN(proj) { //math.IsInf(proj, 1) || math.IsInf(proj, -1) ||
							continue
						}
						heapToAdd := &item{
							value:    new_decision_facet,
							priority: -1 * proj,
						}

						fmt.Println("Decision inside: ")

						projection_general_diff_check(new_decision_facet, x)
						a_abs := AbsVecDense_withsensattremoval(new_decision_facet.a)
						var vproj verifyprojection
						assignment_vproj := verifyprojection{
							Ca:                convert_vecdense_to_frontend(new_decision_facet.a),
							Ca_abs:            convert_vecdense_to_frontend_smallsize(a_abs),
							Cb_extra_scaled:   frontend.Variable(int(math.Round(new_decision_facet.b * math.Pow(roundingcoeff, roundingpower)))),
							Cx0:               convert_intarray_frontendvariable(ix),
							Cprojsq:           frontend.Variable(int(math.Round(proj * proj * math.Pow(roundingcoeff, roundingpower) * math.Pow(roundingcoeff, roundingpower)))),
							Limitsq_eq:        frontend.Variable(int(limits_var.ProjectionDecisionOther)),
							CFieldminusoneby2: frontend.Variable(field_mid)}
						vprojprovetime, vprojverifytime, projproofsize := grothproveverify(&vproj, &assignment_vproj, "projection_decision_loop", file)
						fmt.Println(vprojprovetime, vprojverifytime, projproofsize)

						heap.Push(&facetPotPq, heapToAdd)
						count_facets += 1
						fmt.Fprintln(file, "decision facet, distance: ", -1*proj, new_decision_facet.a, new_decision_facet.b, new_decision_facet.polywhichcreated)
					}
				}

				for i := 0; i < neighborpoly.b.Len(); i++ {
					if slices.Contains(validinds, i) {
						if !seenPolytopes.Contains(flipBitAtIndex(neighborpoly.code, i)) {
							var tempfacet facet_general
							tempa := neighborpoly.A.RawRowView(i)
							tempfacet.a = mat.NewVecDense(len(tempa), tempa)
							tempfacet.b = neighborpoly.b.AtVec(i)
							tempfacet.polywhichcreated = neighborpoly.code
							tempfacet.polywhichcreatedfull = neighborpoly.fullcode
							tempfacet.tight = i
							tempfacet.linearmapa = linearmapa
							tempfacet.linearmapb = linearmapb
							proj, _, _ := projection_general(tempfacet, x)
							if math.IsInf(proj, 1) || math.IsInf(proj, -1) || math.IsNaN(proj) { //math.IsInf(proj, 1) || math.IsInf(proj, -1) ||
								continue
							}
							heapToAdd := &item{
								value:    tempfacet,
								priority: -1 * proj,
							}

							projection_general_diff_check(tempfacet, x)
							a_abs := AbsVecDense_withsensattremoval(tempfacet.a)
							fmt.Println("Verify projection inside loop normal facet")
							var vproj verifyprojection
							assignment_vproj := verifyprojection{
								Ca:                convert_vecdense_to_frontend(tempfacet.a),
								Ca_abs:            convert_vecdense_to_frontend_smallsize(a_abs),
								Cb_extra_scaled:   frontend.Variable(int(math.Round(tempfacet.b * math.Pow(roundingcoeff, roundingpower)))),
								Cx0:               convert_intarray_frontendvariable(ix),
								Cprojsq:           frontend.Variable(int(math.Round(proj * proj * math.Pow(roundingcoeff, roundingpower) * math.Pow(roundingcoeff, roundingpower)))),
								Limitsq_eq:        frontend.Variable(int(limits_var.ProjectionNormalOther)),
								CFieldminusoneby2: frontend.Variable(field_mid)}

							vprojprovetime, vprojverifytime, projproofsize := grothproveverify(&vproj, &assignment_vproj, "projection_normal_loop", file)
							fmt.Println(vprojprovetime, vprojverifytime, projproofsize)
							heap.Push(&facetPotPq, heapToAdd)
							count_facets += 1
							fmt.Fprintln(file, "normal facet, distance: ", -1*proj, tempfacet.a, tempfacet.b, tempfacet.polywhichcreated)
						} else {
							rejected_inds_dict[actual_size_str_code] = append(rejected_inds_dict[actual_size_str_code], fullvalidinddict[i])
							continue
						}
					}
				}
				fmt.Fprintln(file, "Inside not seen polytope")
				fmt.Fprintln(file, "Inside not seen polytopes: ", new_poly_code)
				fmt.Fprintln(file, "Inside not seen polytopes: ", new_poly_code_full)
				seenPolytopes.Add(new_poly_code)
				seenPolytopes_actualcode = append(seenPolytopes_actualcode, actual_size_str_code)
				fmt.Fprintln(file, "Polytope added : ", neighborpoly.code)
				fmt.Fprintln(file, "Newly added polytope A: ", neighborpoly.A)
				fmt.Fprintln(file, "Newly added polytope b: ", neighborpoly.b)
				fmt.Fprintln(file, "New poly decision facets A & b: ", new_decision_facets[0].a, new_decision_facets[0].b)

			}

		}
	}

	data := make(map[string]interface{})

	fmt.Fprintln(file, "Final Seen Polytopes: ", seenPolytopes_actualcode)
	fmt.Fprintln(file, "Number of Total facets checked: ", count_facets)
	fmt.Fprintln(file, "Number of Init facets checked: ", init_facets)
	fmt.Fprintln(file, "Number of seen polytopes: ", seenPolytopes.Cardinality())
	fmt.Fprintln(file, "Radius out: ", radius_output)

	data["Radius"] = radius_output * -1
	data["TotalSeenPolytopes"] = seenPolytopes.Cardinality()
	data["TotalFacetsChecked"] = count_facets

	for key, value := range data {
		// Check if the value is a float64
		if floatValue, isFloat := value.(float64); isFloat {
			// Check if the value is NaN
			if math.IsNaN(floatValue) {
				// Replace NaN with -1
				data[key] = -1.0
			}
		}
	}
	//return data
	return radius_output * -1
}

func main() {
	var limits_var limits
	var testvar testing.T
	var radii []float64

	model_str := "n m" //for eg. "8 16" if the model has two hidden layers of size 8 x 16. do not include final neurons
	dirPath := "/path/to/directory"
	sens_vals := []int{0, 1}
	exePath, _ := os.Getwd()

	limits_json_path := filepath.Join(exePath, "limits.json")
	readlimits(limits_json_path, &limits_var)

	for s := 0; s < len(sens_vals); s++ {

		file, err := os.Create(fmt.Sprintf(dirPath+"/all_logs/outputlog_%d_%s.log", sens_vals[s], model_str))
		if err != nil {
			log.Fatal(err)
		}
		defer file.Close()
		log.SetOutput(file)
		radius := Prove_Verify(&testvar, sens_vals[s], model_str, file, dirPath, limits_var)
		fmt.Println(radius)

		radii = append(radii, radius)
	}

	var minitem int
	r0 := int(radii[0] * math.Pow(roundingcoeff, roundingpower))
	r1 := int(radii[1] * math.Pow(roundingcoeff, roundingpower))

	if r0 <= r1 {
		minitem = r0
	} else {
		minitem = r1
	}

	var vradii VerifyRadiimin
	assignment_vradii := VerifyRadiimin{
		RadiiList: [2]frontend.Variable{frontend.Variable(r0), frontend.Variable(r1)},
		MinItem:   frontend.Variable(minitem)}

	radiiminprovetime, radiiminverifytime, radiiminproofsize := grothproveverify_nofile(&vradii, &assignment_vradii, "Radii_Min")
	fmt.Println(radiiminprovetime, radiiminverifytime, radiiminproofsize)

}
