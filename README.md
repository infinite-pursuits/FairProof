# FairProof

This repository contains the code for the paper [*FairProof* : Confidential and Certifiable Fairness for Neural Networks](https://arxiv.org/pdf/2402.12572), accepted at [ICML 2024](https://icml.cc/virtual/2024/poster/34587).

The main part of the code is in the file *main.go* which contains the function the main function and the *Prove_Verify* function. To run this code, the most important components needed are the model weights, the input point and a dictionary containing a point for each polytope (or the polytopes that we expect to be visited) for the neural network model. The formats for each file are listed at the beginning of the *main.go* file. Some example jsons for each input are also present in the 'example_files' folder. Feel free to change this format (this would also require downstream changes in the way the inputs are read).
