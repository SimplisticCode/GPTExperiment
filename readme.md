# LTL Synthesis using ChatGPT

This repository contains the code used to experiment with generating LTL formulas using ChatGPT. The code is based on the [OpenAI GPT API](https://platform.openai.com/).
The code uses the [Daedulux](https://github.com/samilazregsuidi/Daedalux) tool to generate generate a set of mutants for a given Promela model.
ChatGPT is subsequently used to generate LTL formulas that can distinguish between the original model and the mutants.
Since ChatGPT is not trained on LTL formulas, the generated formulas are not guaranteed to be correct, which means that the 
This workflow is repeated for 
 The mutants are then used to generate LTL formulas using ChatGPT.

## Workflow

The workflow consists of the following steps:
1. Generate a set of mutants for a given Promela model using the Daedalux tool.
2. Use ChatGPT to generate LTL formulas that can distinguish between the original model and the mutants.
3. Evaluate the generated LTL formulas using the [Spin model checker](http://spinroot.com/spin/whatispin.html) using the following steps:
    1. Compile the Original Promela model decorated with the synthesized LTL formula and Macros using Spin.
    2. If the LTL formula is compiled, evaluate each specification using Spin.
        1. If any of the specifications are violated, the LTL formula is incorrect. Improve the generated LTL formula using ChatGPT and repeat the process starting from step 3.1.
        2. If all specifications are satisfied, the LTL formula is correct.
    3. If the LTL formula is not compiled, improve the generated LTL formula using ChatGPT and repeat the process starting from step 3.1.
4. Evaluate the generated LTL formulas on the Mutants using the following steps:
    1. Compile the Promela model decorated with the synthesized LTL formula and Macros using Spin.
    2. Evaluate each LTL property using Spin and note the results (whether the property kills the mutant or not).
5. Compute the mutation score for each of generated LTL formulas.
6. If the mutation score is less than 100%, improve the generated LTL formula using ChatGPT and repeat the process starting from step 3.1.


## Structure
The repository is structured as follows:
- `experiment.py`: The main script for running the experiment.
- `daedalux_runner.py`: A wrapper for the Daedalus tool used to generate mutants and traces.
- `spin_runner.py`: A wrapper for the Spin tool used to evaluate the generated LTL formulas.


- Model: The directory containing the different Promela models used in the experiment.
- Results: The directory containing the results of the experiment.
- Libs: The directory containing the compiled Daedalux tool (The tool is compiled for Linux and MacOS. If you are using Windows, you will need to compile the tool yourself.)

## Requirements

Python 3.6 or later is required. You can install the required packages using the following command:

```bash
pip install -r requirements.txt
```

The tool also requires the [Daedalux](A tool for generating mutants and traces for Promela models) tool to generate mutants and traces for the Promela models. The tool is included in the `libs` directory and is compiled for Linux and MacOS. If you are using Windows, you will need to compile the tool yourself.

The tool also requires the [Spin](http://spinroot.com/spin/whatispin.html) model checker to evaluate the generated LTL formulas. The tool is installed in the docker image used in the experiment. If you are not using the docker image, you will need to install Spin yourself.

## Usage

To generate LTL formulas using ChatGPT, run the following command:

```bash
python3 experiment.py -model_dir <model_dir> -api_key <api_key> 
```

where 
* `<model_dir>` is the path to the directory containing the ChatGPT model 
* `<api_key>` is an API key for the OpenAI API - you can get one by signing up at [OpenAI](https://platform.openai.com/).