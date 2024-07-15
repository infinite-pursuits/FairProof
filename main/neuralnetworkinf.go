package main

import (
	"encoding/json"
	"fmt"
	"gonum.org/v1/gonum/floats"
	"gonum.org/v1/gonum/mat"
	"io/ioutil"
	"os"
	"strconv"
)

type weights struct {
	Weight1 [][]float64 `json:"1.weight"`
	Bias1   []float64   `json:"1.bias"`
	Weight3 [][]float64 `json:"3.weight"`
	Bias3   []float64   `json:"3.bias"`
	Weight5 [][]float64 `json:"5.weight"`
	Bias5   []float64   `json:"5.bias"`
}

type weights_general struct {
	Weights [][][]float64 `json:"weights"`
	Biases  [][]float64   `json:"biases"`
}

func findactivationcode(allweights []*mat.Dense, allbiases []*mat.VecDense, hidden_layer_size []int, x *mat.VecDense) (string, [][]int) {
	activation_code := ""
	activation_code_array := [][]int{}
	tempinp := x

	for hidden_layer := 0; hidden_layer < len(hidden_layer_size); hidden_layer++ {

		r := hidden_layer_size[hidden_layer]
		temp_act_code := []int{}

		dotpdt := mat.NewVecDense(r, nil)
		/*fmt.Println(allweights[hidden_layer].Dims())
		fmt.Println(tempinp.Dims())
		fmt.Println(dotpdt.Dims())*/
		dotpdt.MulVec(allweights[hidden_layer], tempinp)
		//fmt.Println("Dotpdt vec in clear: ", hidden_layer, dotpdt)
		biassum := mat.NewVecDense(r, nil)
		biassum.AddVec(dotpdt, allbiases[hidden_layer]) //prerelu
		//fmt.Println("Biassum in clear: ", hidden_layer, biassum)
		postrelu := mat.NewVecDense(r, nil)

		for i := 0; i < hidden_layer_size[hidden_layer]; i++ {
			if biassum.AtVec(i) >= 0 {
				postrelu.SetVec(i, biassum.AtVec(i))
				activation_code += "1"
				temp_act_code = append(temp_act_code, 1)
			} else {
				postrelu.SetVec(i, 0)
				activation_code += "0"
				temp_act_code = append(temp_act_code, 0)
			}
		}
		tempinp = postrelu
		activation_code_array = append(activation_code_array, temp_act_code)
		//fmt.Println(hidden_layer)
	}
	return activation_code, activation_code_array
}

func inference(allweights []*mat.Dense, allbiases []*mat.VecDense, hidden_layer_size []int, x *mat.VecDense) (int, *mat.VecDense, *mat.VecDense) {
	tempinp := x
	penult := mat.NewVecDense(hidden_layer_size[len(hidden_layer_size)-2], nil)
	var output int
	for hidden_layer := 0; hidden_layer < len(hidden_layer_size); hidden_layer++ {

		r := hidden_layer_size[hidden_layer]

		dotpdt := mat.NewVecDense(r, nil)

		dotpdt.MulVec(allweights[hidden_layer], tempinp)
		biassum := mat.NewVecDense(r, nil)
		biassum.AddVec(dotpdt, allbiases[hidden_layer]) //prerelu
		postrelu := mat.NewVecDense(r, nil)

		if hidden_layer != len(hidden_layer_size)-1 {
			for i := 0; i < hidden_layer_size[hidden_layer]; i++ {
				if biassum.AtVec(i) >= 0 {
					postrelu.SetVec(i, biassum.AtVec(i))
				} else {
					postrelu.SetVec(i, 0)
				}
			}

			if hidden_layer == len(hidden_layer_size)-2 {
				penult = postrelu
				fmt.Println(penult)
			}

		} else {
			for i := 0; i < hidden_layer_size[hidden_layer]; i++ {
				postrelu.SetVec(i, biassum.AtVec(i))
			}
		}

		tempinp = postrelu
	}

	if tempinp.AtVec(0) >= tempinp.AtVec(1) {
		output = 0
	} else {
		output = 1
	}
	//fmt.Println("Final output: ", tempinp)
	return output, tempinp, penult
}

func getpolytopefromcode(activation_code_array [][]int, allweights []*mat.Dense, allbiases []*mat.VecDense, hidden_layer_size []int, total_neurons int, input_size int) (*mat.Dense, *mat.VecDense) {
	polytope_A := mat.NewDense(total_neurons, input_size, nil)
	polytope_b := mat.NewVecDense(total_neurons, nil)

	var wks []*mat.Dense
	var bks []*mat.VecDense

	wks = append(wks, allweights[0])
	bks = append(bks, allbiases[0])

	for i := 1; i < len(hidden_layer_size); i++ {
		//fmt.Println("i: ", i)
		current_wk := wks[len(wks)-1]
		current_bk := bks[len(bks)-1]

		float_activation_code := []float64{}

		for j := 0; j < len(activation_code_array[i-1]); j++ {
			float_activation_code = append(float_activation_code, float64(activation_code_array[i-1][j]))
		}

		current_lambda := mat.NewDiagDense(len(float_activation_code), float_activation_code)
		rpre, _ := allweights[i].Dims()
		_, cpre := current_lambda.Dims()
		precompute := mat.NewDense(rpre, cpre, nil)
		precompute.Mul(allweights[i], current_lambda)

		rpost, _ := precompute.Dims()
		_, cpost := current_wk.Dims()

		new_wk := mat.NewDense(rpost, cpost, nil)
		new_wk.Mul(precompute, current_wk)
		wks = append(wks, new_wk)

		rb, _ := allbiases[i].Dims()
		wb := mat.NewVecDense(rb, nil)
		wb.MulVec(precompute, current_bk)

		final_b := mat.NewVecDense(rb, nil)
		final_b.AddVec(wb, allbiases[i])
		bks = append(bks, final_b)
	}
	count := 0
	for i := 0; i < len(wks); i++ {

		current_wk := wks[i]
		current_bk := bks[i]
		//fmt.Println("i inside", i)

		shifted_activation_code := []float64{}
		for j := 0; j < len(activation_code_array[i]); j++ {
			shifted_activation_code = append(shifted_activation_code, (-2*float64(activation_code_array[i][j]))+1)
		}
		current_j := mat.NewDiagDense(len(shifted_activation_code), shifted_activation_code)
		rcj, ccj := current_j.Dims()
		scaled_current_j := mat.NewDense(rcj, ccj, nil)
		scaled_current_j.Scale(-1, current_j)
		rj, _ := current_j.Dims()
		_, cj := current_wk.Dims()

		a_to_stack := mat.NewDense(rj, cj, nil)
		a_to_stack.Mul(current_j, current_wk)

		b_to_stack := mat.NewVecDense(rj, nil)
		b_to_stack.MulVec(scaled_current_j, current_bk)

		r, _ := a_to_stack.Dims()

		for k := 0; k < r; k++ {
			polytope_A.SetRow(count, a_to_stack.RawRowView(k))
			polytope_b.SetVec(count, b_to_stack.AtVec(k))
			count += 1
		}
	}
	//matPrint(polytope_A)
	//matPrint(polytope_b)
	/*polytope_A_new := mat.NewDense(total_neurons, input_size-1, nil)
	polytope_b_new := mat.NewVecDense(total_neurons, nil)
	_, c := polytope_A.Dims()
	for k := 0; k < polytope_b.Len(); k++ {

		offset_vec := mat.NewVecDense(c, polytope_A.RawRowView(k))
		offset_vec.ScaleVec(sensitiveattributeval, offset_vec)
		offset := mat.Sum(offset_vec)

		polytope_b_new.SetVec(k, polytope_b.AtVec(k)-offset)
	}

	for k := 0; k < polytope_b.Len(); k++ {
		row := polytope_A.RawRowView(k)
		row_firsthalf := row[:sensitiveattributeind]
		row_secondhalf := row[sensitiveattributeind+1:]
		full_row := append(row_firsthalf, row_secondhalf...)
		polytope_A_new.SetRow(k, full_row)
	}*/

	return polytope_A, polytope_b
}

func get_linear_map(activation_code_array [][]int, allweights []*mat.Dense, allbiases []*mat.VecDense, hidden_layer_size []int, total_neurons int, input_size int, x []float64) (*mat.Dense, *mat.VecDense, []float64, int) {
	polytope_A := mat.NewDense(outlogits, input_size, nil)
	polytope_b := mat.NewVecDense(outlogits, nil)

	var wks []*mat.Dense
	var bks []*mat.VecDense

	wks = append(wks, allweights[0])
	bks = append(bks, allbiases[0])

	for i := 1; i < len(hidden_layer_size); i++ {
		//fmt.Println("i: ", i)
		current_wk := wks[len(wks)-1]
		current_bk := bks[len(bks)-1]

		float_activation_code := []float64{}

		for j := 0; j < len(activation_code_array[i-1]); j++ {
			float_activation_code = append(float_activation_code, float64(activation_code_array[i-1][j]))
		}

		current_lambda := mat.NewDiagDense(len(float_activation_code), float_activation_code)
		rpre, _ := allweights[i].Dims()
		_, cpre := current_lambda.Dims()
		precompute := mat.NewDense(rpre, cpre, nil)
		precompute.Mul(allweights[i], current_lambda)

		rpost, _ := precompute.Dims()
		_, cpost := current_wk.Dims()

		new_wk := mat.NewDense(rpost, cpost, nil)
		new_wk.Mul(precompute, current_wk)
		wks = append(wks, new_wk)

		rb, _ := allbiases[i].Dims()
		wb := mat.NewVecDense(rb, nil)
		wb.MulVec(precompute, current_bk)

		final_b := mat.NewVecDense(rb, nil)
		final_b.AddVec(wb, allbiases[i])
		bks = append(bks, final_b)
	}

	for i := 0; i < outlogits; i++ {
		polytope_A.SetRow(i, wks[len(wks)-1].RawRowView(i))
		polytope_b.SetVec(i, bks[len(bks)-1].AtVec(i))
	}
	/*
		count := 0
			all_but_last := 0
			for i := 0; i < len(hidden_layer_size)-1; i++ {
				all_but_last += hidden_layer_size[i]
			}
		start := all_but_last * inputsizeconst
		for i := 0; i < len(wks); i++ {

			current_wk := wks[i]
			current_bk := bks[i]
			//fmt.Println("i inside", i)

			shifted_activation_code := []float64{}
			for j := 0; j < len(activation_code_array[i]); j++ {
				shifted_activation_code = append(shifted_activation_code, (-2*float64(activation_code_array[i][j]))+1)
			}
			current_j := mat.NewDiagDense(len(shifted_activation_code), shifted_activation_code)
			rcj, ccj := current_j.Dims()
			scaled_current_j := mat.NewDense(rcj, ccj, nil)
			scaled_current_j.Scale(-1, current_j)
			rj, _ := current_j.Dims()
			_, cj := current_wk.Dims()

			a_to_stack := mat.NewDense(rj, cj, nil)
			a_to_stack.Mul(current_j, current_wk)

			b_to_stack := mat.NewVecDense(rj, nil)
			b_to_stack.MulVec(scaled_current_j, current_bk)

			if i >= start && i <= start+output_neurons {
				polytope_A.SetRow(count, a_to_stack.RawRowView(i))
				polytope_b.SetVec(count, b_to_stack.AtVec(i))
				count += 1
			}

		}*/

	tempresult := mat.NewVecDense(outlogits, nil)
	xvec := mat.NewVecDense(len(x), x)
	tempresult.MulVec(polytope_A, xvec)
	result := mat.NewVecDense(outlogits, nil)
	result.AddVec(polytope_b, tempresult)
	logits := result.RawVector().Data
	maxIdx := floats.MaxIdx(logits)

	return polytope_A, polytope_b, logits, maxIdx

}

func readfile_weights(fname string, data *weights_general) {
	file, err := os.Open(fname)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer file.Close()

	byteValue, _ := ioutil.ReadAll(file)

	json.Unmarshal(byteValue, data)
}

func readfile_initactivation_code(fname string, actcode *code) {
	file, err := os.Open(fname)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer file.Close()

	byteValue, _ := ioutil.ReadAll(file)

	json.Unmarshal(byteValue, actcode)
}

func readfile_input(fname string, input_size *input) {
	file, err := os.Open(fname)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer file.Close()

	byteValue, _ := ioutil.ReadAll(file)

	json.Unmarshal(byteValue, &input_size)
}

func readfile_layer_sizes(fname string, layer_sizes *layer_sizes_dict) {
	file, err := os.Open(fname)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer file.Close()

	byteValue, _ := ioutil.ReadAll(file)

	json.Unmarshal(byteValue, layer_sizes)
}

func convert_to_matrix(weights_biases weights_general, hidden_layer_size []int, input_size int) ([]*mat.Dense, []*mat.VecDense) {
	var allweights []*mat.Dense
	var biases []*mat.VecDense
	for hidden_layer := 0; hidden_layer < len(hidden_layer_size); hidden_layer++ {

		A := mat.NewDense(hidden_layer_size[hidden_layer], input_size, nil)
		B := mat.NewVecDense(hidden_layer_size[hidden_layer], weights_biases.Biases[hidden_layer])
		for i := 0; i < hidden_layer_size[hidden_layer]; i++ {
			A.SetRow(i, weights_biases.Weights[hidden_layer][i])
		}
		input_size = hidden_layer_size[hidden_layer]
		allweights = append(allweights, A)
		biases = append(biases, B)
	}
	return allweights, biases
}

func flatten_code_array(code [][]int, hiddenlayersize []int) string {
	var strActCode string
	for i, neuroninlayer := range hiddenlayersize {
		for j := 0; j < neuroninlayer; j++ {
			strActCode += strconv.Itoa(code[i][j])
		}
	}
	return strActCode
}

func CheckDecision(f facet_general) bool {
	if f.fType == "decision" {
		return true
	} else {
		return false
	}
}

func stringtostrarray(s string) []string {
	var retarr []string
	for i := 0; i < len(s); i++ {
		retarr = append(retarr, string(s[i]))
	}
	return retarr
}

func findNeighborPolytope(f facet_general) string {
	var newcode string
	newcode = ""
	intarray := stringtostrarray(f.polywhichcreated)
	for i, char := range intarray {
		if i == f.tight {
			if char == "0" {
				newcode += "1"
			} else {
				newcode += "0"
			}
		} else {
			newcode += char
		}
	}
	return newcode
}

func findNeighborPolytopefull(f facet_general) string {
	var newcode string
	newcode = ""
	intarray := stringtostrarray(f.polywhichcreatedfull)
	//fmt.Println("intarray: ", intarray)
	for i, char := range intarray {
		if i == f.tight {
			if char == "0" {
				newcode += "1"
			} else {
				newcode += "0"
			}
		} else {
			newcode += char
		}
	}
	return newcode
}
func flipBitAtIndex(input string, index int) string {
	if index < 0 || index >= len(input) {
		// Invalid index, return the original string
		return input
	}

	// Convert the string to a []byte
	bytes := []byte(input)

	// Flip the bit at the specified index
	if bytes[index] == '0' {
		bytes[index] = '1'
	} else {
		bytes[index] = '0'
	}

	// Convert the []byte back to a string
	result := string(bytes)
	return result
}
func codetoflattenedarray(s string) []int {
	var intarray []int
	stringarray := stringtostrarray(s)
	for _, val := range stringarray {
		if val == "0" {
			intarray = append(intarray, 0)
		} else {
			intarray = append(intarray, 1)
		}
	}
	return intarray
}

func codetolayeredarray(s string, hiddenlayersize []int) [][]int {

	retarr := make([][]int, len(hiddenlayersize))
	flatintarray := codetoflattenedarray(s)
	count := 0
	for i := 0; i < len(hiddenlayersize); i++ {
		retarr[i] = make([]int, hiddenlayersize[i])
		for j := 0; j < hiddenlayersize[i]; j++ {
			retarr[i][j] = flatintarray[count]
			count += 1
		}
	}
	return retarr
}

func readcodeptdict(fname string, code_pt_list *code_pt_dict) {
	file, err := os.Open(fname)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer file.Close()

	byteValue, _ := ioutil.ReadAll(file)

	json.Unmarshal(byteValue, code_pt_list)
	fmt.Println("here")
}

func readfacetptdict(fname string, facet_pt_list *facetpt) {
	file, err := os.Open(fname)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer file.Close()

	byteValue, _ := ioutil.ReadAll(file)

	json.Unmarshal(byteValue, facet_pt_list)
	fmt.Println("here")
}

func readlimits(fname string, limits_var *limits) {
	file, err := os.Open(fname)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer file.Close()

	byteValue, _ := ioutil.ReadAll(file)

	json.Unmarshal(byteValue, limits_var)
}

func readradiusjson(fname string, radius_data *RadiusData) {
	file, err := os.Open(fname)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer file.Close()

	byteValue, _ := ioutil.ReadAll(file)

	json.Unmarshal(byteValue, radius_data)
}

func actual_layersize_code(layered_code [][]int, hiddenlayersize []int) string {
	s := ""
	for i := 0; i < len(hiddenlayersize); i++ {
		for j := 0; j < hiddenlayersize[i]; j++ {
			s += strconv.Itoa(layered_code[i][j])
		}
	}
	return s
}
