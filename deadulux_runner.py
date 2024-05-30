import os
import subprocess

class DeaduluxRunner:   
    """
    A class to generate traces for the given file using Daedalux.
    """
    
    @staticmethod
    def generate_mutants(model :str, num_mutants : int=5):
        """
        Generates mutants for the given original model by calling the mutant generation function in C++.
        
        Args:
        original_model (str): The file path to the original model.
        
        Returns:
        list of str: The list of file paths to the generated mutants.
        """
        # Placeholder for the list of mutants
        mutants = []
    
        command = f"./Libs/daedalux gen-mutants --file {model} --nb_mutants {num_mutants}"
        
        print(f"Generating mutants for model {model}...")
        print(f"Command: {command}")
        
        # Run the command
        result = subprocess.run(command, shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

        # Get the standard output
        stdout_output = result.stdout

        # Parse the output to get the list of generated mutants
        for line in stdout_output.split('\n'):
            if line.endswith('.pml') and os.path.exists(line):
                mutants.append(line)
                
        return mutants
        
    @staticmethod
    def generate_trace(model_path, num_traces, trace_length):
        """
        Calls Daedalux to generate a trace for the given model.
        
        Args:
        model_path (str): The file path to the model.
        num_traces (int): The number of traces to generate.
        trace_length (int): The length of each trace.
        
        Returns:
        list of str: A list of file paths to the generated traces in CSV format.
        """
        
        # Ensure that the model file exists
        if not os.path.exists(model_path):
            raise FileNotFoundError(f"Model file not found: {model_path}")
        
        # Prepare the SPIN command
        command = f"./Libs/daedalux gen-single-traces --file {model_path} --nb_traces {num_traces} --l_traces {trace_length}"
    
        # Run the command
        
        result = subprocess.run(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

        # Get the standard output
        stdout_output = result.stdout

        trace_files = []
        
        # Parse the output to get the list of generated mutants
        for line in stdout_output.split('\n'):
            if line.endswith('.csv') and os.path.exists(line):
                trace_files.append(line)
                
        return trace_files