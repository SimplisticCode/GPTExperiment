import re

class ResponseParser:
    @staticmethod
    def extract_macros_and_ltl_properties_file(file_path):
        """
        Extracts macros and LTL properties from a PROMELA code file and returns them in dictionaries.
        
        Args:
        file_path (str): The path to the PROMELA code file.
        
        Returns:
        tuple: A tuple containing two dictionaries, the first with macros and the second with LTL properties.
        """
        with open(file_path, 'r') as m:
            code = m.read()
            m.close()
            
        return ResponseParser.extract_macros_and_ltl_properties(code)
    
    @staticmethod
    def extract_macros_and_ltl_properties(code):
        """
        Extracts macros and LTL properties from a PROMELA code string and returns them in dictionaries.
        
        Args:
        code (str): A string containing the PROMELA code.
        
        Returns:
        tuple: A tuple containing two dictionaries, the first with macros and the second with LTL properties.
        """
        # Clean up line continuations and excessive whitespace for better regex matching
        cleaned_code = re.sub(r'\s*\\\s*\n\s*', ' ', code)
        
        # Improved regex pattern to match nested parentheses without capturing the final parenthesis
        macro_pattern = r'#define\s+(\w+)\s+\(((?:[^()]+|\((?:[^()]+|\((?:[^()]+|\([^()]*\))*\))*\))*)'
        macro_matches = re.findall(macro_pattern, cleaned_code, re.DOTALL)
        macros = {name: f"({definition.strip()})" for name, definition in macro_matches}

        # Regular expression to match LTL properties
        ltl_pattern = r'ltl\s+(\w+)\s+\{\s*(.*?)\s*\}'
        ltl_matches = re.findall(ltl_pattern, cleaned_code, re.DOTALL)
        ltl_properties = {name: definition.strip() for name, definition in ltl_matches}


        return (macros, ltl_properties)

    
    @staticmethod
    def parse_key_value_pairs(input_string):
        """
        Parses a string containing key-value pairs with nested structures and returns a dictionary.
        This function splits the input string at top-level commas and then extracts keys and values.
        """
        # Remove the outermost curly braces if present
        if input_string.startswith("{") and input_string.endswith("}"):
            input_string = input_string[1:-1].strip()

        # List to hold split parts
        parts = []
        # Temporary part storage
        temp_part = ''
        # Counter for parenthesis depth
        depth = 0

        # Iterate over each character in the string
        for char in input_string:
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1

            # If comma at top level, split here
            if char == ',' and depth == 0:
                parts.append(temp_part.strip())
                temp_part = ''
            else:
                temp_part += char

        # Add the last part if any
        if temp_part:
            parts.append(temp_part.strip())

        # Construct a dictionary from the key-value pairs
        key_value_dict = {}
        for part in parts:
            # Split the part into key and value at the first colon
            if ':' in part:
                key, value = part.split(':', 1)
                key_value_dict[key.strip()] = value.strip()

        return key_value_dict

    @staticmethod
    def find_clause_in_response(response, clause):
        """
        Finds the given clause in the response and returns the content after the clause.
        
        Args:
        response (str): The response from ChatGPT.
        clause (str): The clause to find in the response.
        
        Returns:
        str: The content after the clause in the response.
        """
        start_index = response.index(clause) + len(clause)
        end_index = response.index("}", start_index) + 1
        return response[start_index:end_index].strip()
    
    @staticmethod
    def extract_promela_code(text:str) -> str:
        # Regex pattern to match Promela code blocks
        promela_pattern = re.compile(r"```promela\n(.*?)\n```", re.DOTALL)
        # Extract all matches
        matches = promela_pattern.findall(text)
        
        if not matches:
            quotes_pattern = re.compile(r"```\n(.*?)\n```", re.DOTALL)
            matches = quotes_pattern.findall(text)
            # if no matches found, return the original text
            if not matches:
                return text
            
        #  Otherwise return the longest promela code block
        code = max(matches, key=len, default="")

        return code

    @staticmethod
    def parse_macros_and_specifications(input_text:str) -> tuple:
        """
        Parses the response from ChatGPT to extract the LTL formula.
        The response should contain the macros and the LTL specification.
        
        Args:
        response (str): The response from ChatGPT.
        
        Returns:
        str: The extracted LTL formula.
        """
        # Ensure the input text contains the necessary sections
        if "Macros:" not in input_text or "Specification:" not in input_text:
            # Raise an exception if the response is invalid
            print(input_text)
            raise ValueError("Invalid response format. Missing Macros or Specification section.")
        
        # Find the macros section and extract the macros
        macro_text = ResponseParser.find_clause_in_response(input_text, "Macros:")
        macros = ResponseParser.parse_key_value_pairs(macro_text)
        
        # Find the LTL Specification section and extract the LTL specification
        specification_text = ResponseParser.find_clause_in_response(input_text, "Specification:")
        specifications = ResponseParser.parse_key_value_pairs(specification_text)
        
        return macros, specifications
        