```promela
int array[4];
int i = 0;

active proctype test (){
	do
	:: i < 4 ->
		array[i] = i;
		i++;
	:: else ->
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}

#define is_i_valid (i >= 0 && i <= 4)
#define is_array_valid (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
#define is_array_unchanged (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
#define is_array_step_valid ((i == 0 -> array[0] == 0) && (i == 1 -> array[1] == 1) && (i == 2 -> array[2] == 2) && (i == 3 -> array[3] == 3))
#define is_intermediate_valid ((i == 0 -> array[0] == 0) && (i == 1 -> array[1] == 1) && (i == 2 -> array[2] == 2) && (i == 3 -> array[3] == 3))
#define no_unexpected_modifications (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)

ltl valid_i_range { [] is_i_valid }
ltl eventually_correct_array { <> is_array_valid }
ltl process_terminates_correctly { [] (i == 4 -> is_array_valid) }
ltl array_step_valid { [] is_array_step_valid }
ltl array_unchanged { [] (is_array_valid -> is_array_unchanged) }
ltl intermediate_array_validity { [] is_intermediate_valid }
ltl no_unexpected_modifications { [] no_unexpected_modifications }
```