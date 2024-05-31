import os
import textwrap

from ChatGptClient import Prompt, PromptType
from experiment_result import ExperimentResult
from response_parser import ResponseParser

class QueryBuilder:
    @staticmethod
    def promela_specif_query() -> str:
        guidelines = textwrap.dedent("""
            Guidelines/Criteria:
            - Only Global Variables: Ensure that the LTL properties only refer to global variables and not local variables defined within processes.
            - Temporal Logic Operators: Utilize 'U' (until), '<>' (eventually), and '[]' (always) effectively to express properties.
                - Avoid the 'X' Operator: Instead use 'U' or '<>' to capture future behavior accurately.
            - Variable Values: Remember to handle variable values appropriately, noting that:
                - Variables can only take one value at a time.
                - You can only refer to future values using operators like '<>', 'U', 'W', not past values.
                - Consider default variable values (ints are initialized to 0, bools to false).
            - Process Interleaving: Consider how the interleaving of processes might influence LTL properties.
                - Interleaving may lead to an execution where a process never get the chance to react to a specific event as it gets preempted by another process that removes the event.
                - Ensure that the LTL properties are robust to the interleaving of processes.
                - The classical trick is to add more assumptions in the LTL properties to account for the interleaving.
            - Avoid properties involving that a channel is sending or receiving.
            - State Changes: Two processes cannot change state simultaneously unless they synchronize on a channel.
            - Labels can be used to refer to specific states in the model and be used in the LTL properties. For example, 'critical:' can be a label for a state where a process is in a critical section.
            - Variable ranges: Ensure that LTL properties account for the valid values of variables in the model.
            - Variable Changes: Write properties that capture how variables are allowed to change over time.
            - Array Indexing: Remember that arrays in Promela are zero-indexed, and the last element/index is the size of the array minus one.
            - Non-determinism: Ensure that the LTL properties are robust to the non-deterministic choices in the model.
                - Non-deterministic choices can lead to different executions of the model and should be considered in the LTL properties as nothing is guaranteed to happen.
                - For example, if a process can choose between two actions, the LTL property should not assume a specific choice will ever be made, especially if there is also interleaving in the model.
                - One way to address this problem is to only refer to variables controlled by a single process in the LTL properties.
            - Macros: 
                - Macros are used for complex predicates that cannot expressed directly inside an LTL formula.
                - Macros can only refer to global variables and other macros. Local variables can be passed as arguments to macros.
            - LTL Properties: Ensure that the LTL properties are written in the correct Promela syntax.
                - Operators: true, false, predicates and macros names.
                - Unary operators: '!', '[]', '<>'.
                - Binary operators: '&&', '||', '->', 'U', 'W', 'V', '->', '<->'.
                - Avoid vacuously true properties: like '[] false', 'true U false' or 'p -> p'.
            - Avoid Redundancy:
                - Each macro and LTL property should have a distinct and necessary role in the specification.
                - Two LTL properties should not express the same condition or behavior.
                - Two macros should not have the same definition or purpose.
            - Simple Properties: Break complex properties into multiple simple properties for clarity and ease of understanding.
        """)
        return guidelines

    @staticmethod
    def examples(fullExamples: bool) -> str:
        models = [QueryBuilder.output_example_1_model(), QueryBuilder.output_example_2_model(), QueryBuilder.output_example_3_model()]
        specs = [QueryBuilder.output_example_1_spec(), QueryBuilder.output_example_2_spec(), QueryBuilder.output_example_3_spec()]
        if fullExamples:
            return QueryBuilder.build_entire_models_specs(models, specs)
        else:
            return QueryBuilder.build_models_specs(models, specs)
    
    @staticmethod
    def build_model_with_spec(model:str, spec:str) -> str:
        macros, specifications = ResponseParser.parse_macros_and_specifications(spec)
        for macro in macros:
            model += f'\n#define {macro} {macros[macro]}'
        for spec in specifications:
            ltl_formula = f'ltl {spec} {{ {specifications[spec]} }}'
            model += f'\n{ltl_formula}'
        return model

    @staticmethod
    def build_models_specs (models: list, specs: list) -> str:
        query_parts = []
        for i, model in enumerate(models):
            query_parts.append(f"Model {i + 1}:\n")
            query_parts.append(model + "\n")
            query_parts.append(f"Specification {i + 1}:\n")
            query_parts.append(specs[i] + "\n")
        query = "".join(query_parts)
        return query
    
    def build_entire_models_specs (models: list, specs: list) -> str:
        query_parts = []
        for i, model in enumerate(models):
            query_parts.append(f"Example {i + 1}:\n")
            entire_model = QueryBuilder.build_model_with_spec(model, specs[i])
            query_parts.append(entire_model)
        query = "".join(query_parts)
        return query    
    
    @staticmethod
    def output_format_query() -> str:
        output_format = textwrap.dedent("""
            Output Format:
            Macros: {A map of key-value pair linking each macro name to its definition in SPIN's syntax}. For example, {is_red: (state == red), is_yellow: (state == yellow)}.
            Specification: {A map of key-value pair linking each LTL property to its definition in SPIN's syntax}. For example, {always_red: [] is_red, eventually_green: <> is_green}.
            Bisimilarity: {A list of mutants that are bisimilar to the original model}.
            DO NOT include anything else in the output and DO NOT use quotes around the macro names or definitions.
            
            Output Example:
            Macros: {is_red: (state == red), is_yellow: (state == yellow), x_gt_5: (x > 5)}
            Specification: {red_until_yellow: [] is_red -> (is_red U is_yellow), always_red: [] is_red, eventually_yellow: <> is_yellow}
            Bisimilarity: {mutant1.pml, mutant2.pml}
        """)
        return output_format
    
    @staticmethod
    def output_format_model(add_examples : bool) -> str:
        output_format = textwrap.dedent("""
            Output Format:
            {The corrected Promela model with the macros and LTL properties integrated}.
            DO NOT include anything else in the output and DO NOT use quotes around the macro names, definitions, or LTL properties.
        """)
        
        if add_examples:
            return output_format + "\n\n" + QueryBuilder.examples(False)
        else:
            return output_format
    
        
    @staticmethod
    def output_example_1_model() -> str:
        model = textwrap.dedent("""
            mtype = {green, yellow, red}
            mtype state = red;
            active proctype foo() {
                do
                :: state == red -> state = green;
                :: state == green -> state = yellow;
                :: state == yellow -> state = red;
                od;
            }
        """)
        return model
    
    @staticmethod
    def output_example_1_spec() -> str:
        return textwrap.dedent(""" 
            Macros: {is_red: (state == red), is_yellow: (state == yellow), is_green: (state == green)}
            Specification: {red_until_yellow: [] is_red -> (is_red U is_yellow), cycles_through_all: ([] <> is_red && [] <> is_green && [] <> is_yellow)
            Bisimilarity: {mutant1.pml, mutant2.pml}
        """)
   
    @staticmethod
    def output_example_2_model() -> str:
        example = textwrap.dedent("""
            mtype = {levelMsg, stop, methanestop, alarm, running, commandMsg, start, alarmMsg, high, low, stopped, medium, ready, lowstop}
            chan cCmd = [0] of {mtype};
            chan cAlarm = [0] of {mtype};
            chan cMethane = [0] of {mtype};
            chan cLevel = [0] of {mtype};
            mtype pstate = stopped;
            mtype readMsg = commandMsg;
            bool pumpOn = false;
            bool methane = false;
            mtype waterLevel = medium;
            mtype uwants = stop;
            mtype level = medium;

            active proctype controller(){
                mtype pcommand = start;
                do
                ::	atomic {
                        cCmd?pcommand;
                        readMsg = commandMsg;
                    };
                    if
                    ::	pcommand == stop;
                        if
                        ::	atomic {
                                pstate == running;
                                pumpOn = false;
                            };
                        ::	else;
                            skip;
                        fi;
                        pstate = stopped;
                    ::	pcommand == start;
                        if
                        ::	atomic {
                                pstate != running;
                                pstate = ready;
                            };
                        ::	else;
                            skip;
                        fi;
                    ::	else;
                        assert((false));
                    fi;
                    cCmd!pstate;
                ::	atomic {
                        cAlarm?_;
                        readMsg = alarmMsg;
                    };
                    if
                    ::	atomic {
                            pstate == running;
                            pumpOn = false;
                        };
                    ::	else;
                        skip;
                    fi;
                    pstate = methanestop;
                ::	atomic {
                        cLevel?level;
                        readMsg = levelMsg;
                    };
                    if
                    ::	level == high;
                        if
                        ::	pstate == ready || pstate == lowstop;
                            atomic {
                                cMethane!pstate;
                                cMethane?pstate;
                                if
                                ::	pstate == ready;
                                    pstate = running;
                                    pumpOn = true;
                                ::	else;
                                    skip;
                                fi;
                            };
                        ::	else;
                            skip;
                        fi;
                    ::	level == low;
                        if
                        ::	atomic {
                                pstate == running;
                                pumpOn = false;
                                pstate = lowstop;
                            };
                        ::	else;
                            skip;
                        fi;
                    ::	level == medium;
                        skip;
                    fi;
                od;
            }
            active proctype user(){
                do
                ::	
                atomic {
                    if
                    ::	uwants = start;
                    ::	uwants = stop;
                    fi;
                    cCmd!uwants;
                    cCmd?_;
                };
                od;
            }
            active proctype methanealarm(){
                do
                ::	methane = true;
                    cAlarm!alarm;
                ::	methane = false;
                od;
            }
            active proctype methanesensor(){
                do
                ::	atomic {
                        cMethane?_;
                        if
                        ::	methane;
                            cMethane!methanestop;
                        ::	!methane;
                            cMethane!ready;
                        fi;
                    };
                od;
            }
            active proctype watersensor(){
                do
                ::	atomic {
                        if
                        ::	waterLevel == low;
                            if
                            ::	waterLevel = low;
                            ::	waterLevel = medium;
                            fi;
                        ::	waterLevel == medium;
                            if
                            ::	waterLevel = low;
                            ::	waterLevel = medium;
                            ::	waterLevel = high;
                            fi;
                        ::	waterLevel == high;
                            if
                            ::	waterLevel = medium;
                            ::	waterLevel = high;
                            fi;
                        fi;
                        cLevel!waterLevel;
                    };
                od;
            }
        """)
        return example
    
    
    @staticmethod
    def output_example_2_spec() -> str:
        spec = textwrap.dedent("""
        Macros: {
            is_lowstop: (pstate == lowstop), is_commandMsg: (readMsg == commandMsg), is_alarmMsg: (readMsg == alarmMsg),is_levelMsg: (readMsg == levelMsg),
            is_high: (level == high),
            is_medium: (level == medium),
            is_low: (level == low),
            pump_on: (pumpOn == true),
            pump_off: (pumpOn == false),
            methane_present: (methane == true),
            methane_absent: (methane == false),
            user_wants_start: (readMsg == start),
            user_wants_stop: (readMsg == stop)
        }
        Specification: {
            valid_pstate: [](is_stopped || is_running || is_ready || is_methanestop || is_lowstop),
            valid_readMsg: [](is_commandMsg || is_alarmMsg || is_levelMsg),
            valid_waterLevel: [](is_high || is_medium || is_low),
            valid_pumpOn: [](pump_on || pump_off),
            alarm_leads_to_stop: [](is_alarmMsg -> <> pump_off),
            user_start_leads_to_ready_or_running: [](user_wants_start -> (user_wants_start U (is_ready || is_running))),
            user_stop_leads_to_pump_off: [](user_wants_stop -> <> pump_off),
            pump_on_system_running: [](pump_on -> is_running),
            low_water_level_leads_to_pumpstop: []((is_levelMsg && is_low) -> <> pump_off),
            high_water_level_leads_to_pumpstart: []((is_levelMsg && is_high) -> <> (pump_on || is_methanestop)),
            high_metane_leads_to_pumpstop: [](is_methanestop -> <> pump_off)
        }
        Bisimilarity: []
        """)
        return spec
    
    @staticmethod
    def output_example_3_model():
        example = textwrap.dedent("""
            mtype = {red, yellow, green}
            mtype state1 = red;
            mtype state2 = green;
            active proctype light1(){
                do
                :: state1 == red && state2 == yellow;
                    state1 = green;
                :: state1 == green && state2 == red;
                    state1 = yellow;
                :: state2 == yellow && state2 == green;
                    state1 = red;
                od;
            }
            active proctype light2(){
                do
                :: state2 == red && state1 == yellow;
                    state2 = green;
                :: state2 == green && state1 == red;
                    state2 = yellow;
                :: state2 == yellow && state1 == green;
                    state2 = red;
                od;
            }
        """)
        return example
    
    @staticmethod 
    def output_example_3_spec() -> str:
        return textwrap.dedent("""
            Macros: {
                is_red1: (state1 == red),
                is_yellow1: (state1 == yellow),
                is_green1: (state1 == green),
                is_red2: (state2 == red),
                is_yellow2: (state2 == yellow),
                is_green2: (state2 == green)
            }
            Specification: {
                always_valid_states: [] (is_red1 || is_yellow1 || is_green1) && (is_red2 || is_yellow2 || is_green2),
                red1_until_green1: [] is_red1 -> (is_red1 U is_green1),
                green1_until_yellow1: [] is_green1 -> (is_green1 U is_yellow1),
                yellow1_until_red1: [] is_yellow1 -> (is_yellow1 U is_red1),
                red2_until_green2: [] is_red2 -> (is_red2 U is_green2),
                green2_until_yellow2: [] is_green2 -> (is_green2 U is_yellow2),
                yellow2_until_red2: [] is_yellow2 -> (is_yellow2 U is_red2),
                eventually_green1: <> is_green1,
                eventually_yellow1: <> is_yellow1,
                eventually_red1: <> is_red1,
                eventually_green2: <> is_green2,
                eventually_yellow2: <> is_yellow2,
                eventually_red2: <> is_red2,
                mutual_exclusion: [] !(is_green1 && is_green2)
            }
            Bisimilarity: []
        """)
    
    @staticmethod
    def output_example4():
        example = textwrap.dedent("""
        #define NUM_PASS 3
        #define MAX_PASS 2
        #define HEIGHT 4

        mtype = {
                /* common state*/
            WAIT,

            /* passenger state */
            GETON,
            GETOFF,
            
            /* elevator state */
            MOVE_UP,
            MOVE_DOWN,
            FLOOR,
        };


        typedef Object
        {
            /* common fields */
            mtype state = WAIT;
            mtype last_state = WAIT;
            byte floor = 0;			// bit wise current floor
        
            /* elevator fields */
            byte stopping_floors = 0;		// bit wise floors to be stopping
            byte number_of_passengers = 0;	// count wise

            /* passenger fields */
            byte destination = 0;		// bit wise destination
            short id = 0;			// bit wise id
            
        };

        byte participation = 0;			// bit wise
        byte turn = 0;				// bit wise
        Object elevator;


        inline echo1() {
            printf("passenger.state :%e, turn :%d, passenger.id :%d  stopping_floors:%d, floor:%d\n",passenger.state, turn, passenger.id, elevator.stopping_floors , elevator.floor);
        }

        inline echo2() {
            printf("elevator.state :%e, turn :%d, elevator   stopping_floors:%d, floor:%d\n",elevator.state, turn, elevator.stopping_floors , elevator.floor);
        }

        proctype Passenger(Object passenger)
        {

        participation = participation | passenger.id;
        do
            :: passenger.state == WAIT -> wait: 
            (turn & passenger.id) > 0;
            atomic {
                if
                :: passenger.floor == elevator.floor && elevator.number_of_passengers < MAX_PASS ->  { 
                    passenger.state = GETON;
                    elevator.number_of_passengers++;
                    elevator.stopping_floors = elevator.stopping_floors | passenger.destination;
                }
                :: else -> elevator.stopping_floors = elevator.stopping_floors | passenger.floor;
                fi;
                echo1();
                turn = turn - passenger.id;
            };
            :: passenger.state == GETON -> geton: 
            (turn & passenger.id) > 0;
            atomic {
                if
                :: passenger.destination == elevator.floor ->  { 
                    passenger.state = GETOFF;
                    elevator.number_of_passengers--;
                }
                :: else -> skip;
                fi;
                echo1();
                turn = turn - passenger.id;
            };
            :: passenger.state == GETOFF -> getoff: 
            (turn & passenger.id) > 0;
            atomic { 
                participation = participation - passenger.id;
                turn = turn - passenger.id;
                echo1();
                break;
            }
        od;

        printf("-------------------process is ended, passenger.id :%d ------------------\n", passenger.id );
        };


        proctype Elevator()
        {
        do
            :: elevator.state == WAIT -> 
            turn == 0;
            atomic {
                if
                :: elevator.stopping_floors > 0 && elevator.stopping_floors > elevator.floor  -> elevator.state = MOVE_UP; elevator.last_state = WAIT;
                :: elevator.stopping_floors > 0 && elevator.stopping_floors < elevator.floor && elevator.floor > 1 -> elevator.state = MOVE_DOWN; elevator.last_state = WAIT;

                :: else -> skip;
                fi;
                echo2();
                turn = participation;
            };
            :: elevator.state == MOVE_UP -> 
            turn == 0;
            atomic {
                elevator.floor = elevator.floor << 1;
                elevator.stopping_floors = (elevator.stopping_floors ^ elevator.floor) & elevator.stopping_floors;
                elevator.state = FLOOR; elevator.last_state = MOVE_UP;
                echo2();
                turn = participation;
            };
            :: elevator.state == MOVE_DOWN ->
            turn == 0;
            atomic {
                elevator.floor = elevator.floor >> 1;
                elevator.stopping_floors = (elevator.stopping_floors ^ elevator.floor) & elevator.stopping_floors;
                elevator.state = FLOOR; elevator.last_state = MOVE_UP;
                echo2();
                turn = participation;
            };
            :: elevator.state == FLOOR -> 
            turn == 0;
            atomic {
                if
                :: elevator.last_state == MOVE_UP && elevator.stopping_floors > elevator.floor  -> elevator.state = MOVE_UP;
                :: elevator.last_state == MOVE_UP && elevator.stopping_floors < elevator.floor  -> elevator.state = MOVE_DOWN;
                :: elevator.last_state == MOVE_DOWN && elevator.stopping_floors & (elevator.floor-1) > 0 -> elevator.state = MOVE_DOWN;
                :: elevator.last_state == MOVE_DOWN && elevator.stopping_floors & (elevator.floor-1) == 0 && elevator.stopping_floors > 0 -> elevator.state = MOVE_UP;
                :: else -> elevator.state = WAIT;
                fi;
                echo2();
                turn = participation;
            };
        od;
        };

        init {

            Object passenger1;
            passenger1.id = 1;
            passenger1.floor=2;
            passenger1.destination=4;

            Object passenger2;
            passenger2.id = 2;
            passenger2.floor=4;
            passenger2.destination=1;
            
            Object passenger3;
            passenger3.id = 4;
            passenger3.floor=1;
            passenger3.destination=8;
            
            Object passenger4;
            passenger4.id = 8;
            passenger4.floor=1;
            passenger4.destination=4;
            
            run Passenger(passenger1);
            run Passenger(passenger2);
            run Passenger(passenger3);
            run Passenger(passenger4);
            
            elevator.floor = 1;
            run Elevator();
        }
        """)
        return example
                                         

                            
    @staticmethod
    def append_model(query_parts : list, file_path : str):
        """"
        Appends the original model and mutants to the query parts and joins them to return a complete query.
        
        Args:
        query_parts (list of str): The list of query parts to append to.
        original_model (str): The file path to the original model.
        mutants (list of str): The list of file paths to the mutants.
        
        Returns:
        str: The complete query string.
        """
        #Ensure the original model exists
        if not os.path.exists(file_path):
            raise FileNotFoundError(f"The model file does not exist: {file_path}")
        
        with open(file_path, 'r') as file:
            query_parts.append(file.read() + "\n")
            
    @staticmethod
    def append_promela_models(original_model, mutants) -> str:
        """"
        Appends the original model and mutants to the query parts and joins them to return a complete query.
        
        Args:
        query_parts (list of str): The list of query parts to append to.
        original_model (str): The file path to the original model.
        mutants (list of str): The list of file paths to the mutants.
        
        Returns:
        str: The complete query string.
        """
        query_parts = []
        query_parts.append("Original Model:\n")
        QueryBuilder.append_model(query_parts, original_model)
            
        for i, mutant in enumerate(mutants):
            query_parts.append(f"Mutant {i + 1}:\n")
            QueryBuilder.append_model(query_parts, mutant)
            
        query = "".join(query_parts)
        return query
            
    @staticmethod
    def build_standard_query(model : str, mutants: list, add_examples : bool) -> Prompt:
        query_parts = []
        objective = textwrap.dedent("""
            Objective: Develop a concise and intuitive LTL specification to distinguish the original Promela model from its mutants.
            The specification should accurately capture the intended behavior of the original model and differentiate it from the mutants.
            Steps to Follow:
            Step 1. Understand the intention of the original model and the key states and transitions it should exhibit.
            Step 2. Find all possible values for each of the global variables in the model.
            Step 3. Formulate invariants that capture the valid values of the global variables throughout the model's execution.
            Step 4. Go through each mutant and identify the specific behavior that distinguishes it from the original model.
            Step 5. Asses whether any of the mutants are bisimilar to the original model.
            Step 6. Develop an LTL property for each mutant that captures a property violated by the mutant but satisfied by the original model.
            Step 7: Check that all LTL properties are written in the correct Promela syntax and are concise and clear.
            Step 8. Remove redundant or unnecessary properties to streamline the specification.
            Step 9. Sort the LTL properties in order of complexity, starting with the simplest properties first capturing the properties describing the possible values of the global variables.
            Step 10. Ensure that the LTL properties are written in the correct Promela syntax and are concise and clear.
            Step 11. Define Relevant Macros: Create macros for conditions not directly supported in LTL. Name each macro descriptively in lowercase.
            Step 12: Create Return Format: Combine the defined macros and properties into a formal SPIN syntax specification in the specified format.
        """)
        query_parts.append(objective)
        query_parts.append(QueryBuilder.promela_specif_query())
        query_parts.append(QueryBuilder.append_promela_models(model, mutants))
        query_parts.append(QueryBuilder.output_format_query())
        if add_examples:
            query_parts.append(QueryBuilder.examples(False))
        query = "".join(query_parts)
        prompt = Prompt(query, PromptType.CREATE_Specification, model)
        return prompt        
    
    @staticmethod
    def construct_feedback_query(objective: str, model : str, spinFeedback : str, add_examples : bool, promptType : PromptType) -> Prompt:
        query_parts = []
        query_parts.append(objective)
        query_parts.append(QueryBuilder.promela_specif_query())
        outputFormat = QueryBuilder.output_format_model(add_examples)
        query_parts.append(outputFormat)
        query_parts.append("Model to Fix:\n")
        QueryBuilder.append_model(query_parts, model)
        query_parts.append("The result of running SPIN on the provided model is:\n")
        query_parts.append(spinFeedback)
        
        query = "".join(query_parts)
        prompt = Prompt(query, promptType, model)
        return prompt
        
    @staticmethod
    def fix_compilation_query(model : str, spinFeedback : str, add_examples : bool) -> Prompt:
        """
        This function constructs a query for ChatGPT to fix the compilation error in the provided Promela model based on the feedback from the SPIN model checker.
        
        Args:
        model (str): The file path to the original model.
        spinFeedback (str): The feedback from the SPIN model checker.
        save (bool): A flag to save the query to a file.
        
        Returns:
        str: The constructed query.
        """
        objective = textwrap.dedent("""
            Objective: Fix the compilation error in the provided Promela model based on the feedback from the SPIN model checker.
            Steps to Follow:
            Step 1. Review the Compilation Error to determine the cause of the issue.
            Step 2. Modify the faulty definition or property to resolve the compilation error.
            Step 3. Go through all the LTL properties and macros in the model and sort them in order of complexity starting with the simplest properties first.
            Step 4. Remove any redundant or unnecessary properties to streamline the model.
            Step 5. Ensure that the remaining LTL properties are written in the correct Promela syntax.
            Step 6. Ensure that all macros and LTL properties are correctly defined and do not conflict with each other and is satisfied by the model.
            Step 7. Integrate the corrected LTL properties and macros into the model.
            """)
        prompt = QueryBuilder.construct_feedback_query(objective, model, spinFeedback, add_examples, PromptType.FIX_CompileError)
        return prompt
    
    @staticmethod
    def fix_verification_query(model : str, 
                               spinFeedback : str, 
                               counterExample : str, 
                               add_examples : bool,
                               previously_satisfied_specs : dict, 
                               previously_failed_specs : dict) -> Prompt:
        """
        This function constructs a query for ChatGPT to fix the compilation error in the provided Promela model based on the feedback from the SPIN model checker.
        
        Args:
        model (str): The file path to the original model.
        spinFeedback (str): The feedback from the SPIN model checker.
        counterExample (str): The counterexample generated by SPIN.
        previously_failed_specs (dict): A dictionary containing the previously failed LTL properties and their corresponding counterexamples.
        
        Returns:
        str: The constructed query.
        """
        objective = textwrap.dedent("""
            Objective: Fix the verification error in the provided Promela model using feedback from the SPIN model checker.
            Steps to Follow:
            Step 1: Analyze the Verification Error to understand the cause of the issue to identify the problematic LTL property.
            Step 2: Consult the counterexample generated by SPIN to identify the behavior that violates the LTL property.
            Step 3: Correct the LTL property to ensure that it is satisfied by the model - DO NOT change other properties.
            Step 4: Ensure that the corrected LTL property is valid and does not conflict with other properties.
            Step 5: Sort the LTL properties in order of complexity, starting with the simplest properties first (e.g., invariant properties over the global variables).
            Step 6: Integrate the corrected LTL property into the model.
        """)
        
        spinFeedback += "\n\nCounterexample:\n" + counterExample
        prompt = QueryBuilder.construct_feedback_query(objective, model, spinFeedback, add_examples, PromptType.FIX_VerificationError)
        
        # if len(previously_satisfied_specs) > 1:
        #     previously_satisfied_specs_str = "\nThe following LTL properties were previously satisfied by the model:\n"
        #     for name, spec in previously_satisfied_specs.items():
        #         previously_satisfied_specs_str += f"{name}:{spec}\n"
        #     prompt.text += previously_satisfied_specs_str
        # previously_failed_specs_str = "The following LTL properties have been checked by SPIN and failed in the model:\n"
        # for name, spec in previously_failed_specs.items():
        #     previously_failed_specs_str += f"{name}:{spec}\n"
        return prompt
    
    @staticmethod
    def create_specification_query(model, trace_files, add_examples : bool) -> Prompt:
        query_parts = []

        objective = textwrap.dedent("""
        Objective: Your task is create an LTL specification that captures the behavior of a Promela model.        
        Steps to Follow:
        Step 1: Analyze the Model: Review the Promela model to understand its behavior, the state space, and the key variables and processes.
        Step 2: Identify Global Variables: Identify the global variables in the model and their possible values.
        Step 3: Formulate Invariants: Develop LTL properties that capture the valid values of the global variables throughout the model's execution.
        Step 4: Formulate Temporal Properties: Create LTL properties that express the key features of the model, such as state transitions and process interleaving.
        Step 5: Define Macros: Create macros for conditions not directly supported in LTL. Name each macro descriptively in lowercase.
        Step 6: Check Validity: Ensure that all LTL properties are written in the correct Promela syntax and are concise and clear.
        Step 7: Check Correctness: Verify that the LTL properties are satisfied by the model.
        Step 8: Sort Properties: Sort the LTL properties in order of complexity, starting with the simplest properties first.
        Step 9: Define Return Format: Combine the defined macros and properties into a formal SPIN syntax specification in the specified format.
        """)
        
        query_parts.append(objective)
        query_parts.append(QueryBuilder.promela_specif_query())
        query_parts.append(QueryBuilder.output_format_query())
        if add_examples:
            query_parts.append(QueryBuilder.examples(False))

        query_parts.append("Original Model:\n")
        QueryBuilder.append_model(query_parts, model)
        
        number_of_traces = len(trace_files)
        if number_of_traces > 0:
            query_parts.append(f"{number_of_traces} traces have been provided in CSV format. Each trace represents a possible execution path of the model.\n")
            for i, trace in enumerate(trace_files):
                query_parts.append(f"Trace {i + 1}:\n")
                with open(trace, 'r') as file:
                    query_parts.append(file.read() + "\n")
                    query_parts.append("\n")
            
        query = "".join(query_parts)
        prompt = Prompt(query, PromptType.CREATE_Specification, model)
        return prompt
    
    @staticmethod
    def enhance_specification_query(model : str, surviving_mutants : str, specifications : list) -> Prompt:
        query_parts = []

        objective = textwrap.dedent("""
        Objective: Your task is to enhance the existing LTL specifications for a Promela model to improve the verification results and eliminate the remaining mutants.
        You should analyze the existing LTL properties and the surviving mutants to identify areas for improvement and refinement and add new properties to cover the identified gaps.
        Steps to Follow:
        Step 1: Analyze the LTL Properties: Review the LTL properties to identify why they have not killed the surviving mutants.
        Step 2: Develop LTL Properties: Develop LTL properties to kill the surviving mutants.
        Step 3: Complement Existing Properties: Ensure that the new LTL properties complement the existing ones and do not replace or conflict with them.
        Step 4: Ensure Correctness: Verify that the new LTL properties are written in the correct Promela syntax and that they are satisfied by the model.
        Step 5: Sort LTL Properties: Sort the LTL properties in order of complexity, starting with the simplest properties first (e.g., invariant properties).
        """)
        query_parts.append(objective)
        query_parts.append(QueryBuilder.promela_specif_query())
        query_parts.append(QueryBuilder.output_format_query())

        query_parts.append("The original model and the mutants below both satisfy provided LTL properties.\n")
        query_parts.append(QueryBuilder.append_promela_models(model, surviving_mutants))
        
        specification_parts = textwrap.dedent("""
                                                The existing LTL properties have already been used to kill some mutants (which are not provided here).
                                                Consequently, these properties should not be modified or removed, as they are effective in distinguishing the original model from some mutants.
                                                The following LTL properties that you should not modify are:
                                              """)
        
        specification_parts += "\n".join(specifications)
        query_parts.append(specification_parts)
        
        query = "".join(query_parts)
        prompt = Prompt(query, PromptType.ENHANCE_Specification, model)
        return prompt       
    
        
    @staticmethod
    def simplify_formulas_query(model : str, experiment_result : ExperimentResult) -> Prompt:
        query_parts = []

        objective = textwrap.dedent("""
        Background: You have successfully created an LTL specification capable of distinguishing the original Promela model from its mutants.
        Objective: Your task is to simplify the existing LTL specification to make it more concise and easier to understand while maintaining its correctness.
        The goal is to reduce the complexity of the LTL properties without compromising their ability to distinguish the original model from the mutants.
        Steps to Follow:
        Step 1: Review the Existing LTL Properties: Analyze the existing LTL properties to identify redundant or overly complex properties.
        Step 2: Study the Experiment Results: Review the experiment results to understand which mutants a specific LTL property kills 
            a) Properties that kill many mutants are essential and should be kept.
            b) Properties that kill zero mutants are redundant and can be removed.
            c) Two properties that kill the same mutants are redundant, and can be combined or simplified.
            d) Properties that kill only a few mutants may need to be refined or combined with other properties.
        Step 3: Simplify LTL Properties: Simplify the LTL properties by removing redundancies, combining similar properties, and refining complex properties.
        Step 4: Ensure Correctness: Verify that the simplified LTL properties are written in the correct Promela syntax and that they are satisfied by the model.
        Step 5: Sort LTL Properties: Sort the LTL properties in order of complexity, starting with the simplest properties first.
        """)
        query_parts.append(objective)
        query_parts.append(QueryBuilder.promela_specif_query())
        query_parts.append(QueryBuilder.output_format_query())
        
        query_parts.append("Model with Specifications to Simplify:\n")
        QueryBuilder.append_model(query_parts, model)
        
        query_parts.append("Experiment Results:\n")
        for spec in experiment_result.specificationDict:
            killed_mutant_names = [os.path.basename(mutant) for mutant in spec.killed_mutants]
            query_parts.append(f"Specification: {spec.specification}, Number of Killed Mutants: {spec.num_killed_mutants} - {killed_mutant_names} Mutation Score: {spec.mutation_score}\n")

        query = "".join(query_parts)
        prompt = Prompt(query, PromptType.ENHANCE_Specification, model)
        return prompt       