#define is_correct_array (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
#define is_valid_i (i >= 0 && i <= 4)
#define is_i_4 (i == 4)
ltl valid_index { [] is_valid_i }
ltl eventually_correct_array_0 { <> (array[0] == 0) }
ltl eventually_correct_array_1 { <> (array[1] == 1) }
ltl eventually_correct_array_2 { <> (array[2] == 2) }
ltl eventually_correct_array_3 { <> (array[3] == 3) }
ltl final_assertion { [] (is_i_4 -> is_correct_array) }
ltl always_correct_array_0 { [] (array[0] == 0) }
ltl always_correct_array_2 { [] (array[1] <= 1) }
ltl eventually_correct_array { <> is_correct_array }
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