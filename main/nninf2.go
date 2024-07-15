package main

import (
	"encoding/json"
	"fmt"
	"gonum.org/v1/gonum/floats"
	"io/ioutil"
	"os"
)

func nninf2main() {
	x := []float64{0.8, 0.7}
	fname := "/Users/chhaviyadav/Desktop/geometric-certificates/examples/weights.json"
	var data weights

	file, err := os.Open(fname)
	if err != nil {
		fmt.Println(err)
		return
	}
	defer file.Close()

	byteValue, _ := ioutil.ReadAll(file)

	json.Unmarshal(byteValue, &data)

	w1 := data.Weight1
	b1 := data.Bias1
	w2 := data.Weight3
	b2 := data.Bias3
	//w3 := data.Weight5
	//b3 := data.Bias5

	activation_code := []int{}
	next_layer_pre := []float64{}
	next_layer_post := []float64{}
	for i := 0; i < 5; i++ {
		next_layer_pre = append(next_layer_pre, floats.Dot(w1[i], x)+b1[i])
		if next_layer_pre[i] >= 0 {
			next_layer_post = append(next_layer_post, next_layer_pre[i])
			activation_code = append(activation_code, 1)
		} else {
			next_layer_post = append(next_layer_post, 0)
			activation_code = append(activation_code, 0)
		}

	}
	fmt.Println(activation_code)
	fmt.Println(next_layer_post)

	activation_code2 := []int{}
	next_layer_pre2 := []float64{}
	next_layer_post2 := []float64{}

	for i := 0; i < 3; i++ {
		next_layer_pre2 = append(next_layer_pre2, floats.Dot(w2[i], next_layer_post)+b2[i])
		if next_layer_pre2[i] >= 0 {
			next_layer_post2 = append(next_layer_post2, next_layer_pre2[i])
			activation_code2 = append(activation_code2, 1)
		} else {
			next_layer_post2 = append(next_layer_post2, 0)
			activation_code2 = append(activation_code2, 0)
		}

	}

	total_act_code := append(activation_code, activation_code2...)
	fmt.Println(total_act_code)

}
