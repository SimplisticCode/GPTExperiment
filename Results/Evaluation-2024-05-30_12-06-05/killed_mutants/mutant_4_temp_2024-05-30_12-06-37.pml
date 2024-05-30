#define is_array0_correct (array[0] == 0)
#define is_array1_correct (array[1] == 1)
#define is_array2_correct (array[2] == 2)
#define is_array3_correct (array[3] == 3)
#define is_i_within_bounds (i >= 0 && i <= 4)
ltl valid_i { [] is_i_within_bounds }
ltl eventually_i_4 { <> (i == 4) }
ltl eventually_array0_correct { <> is_array0_correct }
ltl eventually_array1_correct { <> is_array1_correct }
ltl eventually_array2_correct { <> is_array2_correct }
ltl eventually_array3_correct { <> is_array3_correct }
ltl assert_correct_array { [] (i == 4 -> (is_array0_correct && is_array1_correct && is_array2_correct && is_array3_correct)) }
int array[4];
int i = 0;
active proctype test(){
	do
	:: i < 4;
		array[i] = array[3];
		i++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
