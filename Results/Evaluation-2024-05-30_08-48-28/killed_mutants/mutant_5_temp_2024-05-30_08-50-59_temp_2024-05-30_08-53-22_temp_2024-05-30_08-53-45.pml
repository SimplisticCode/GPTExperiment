#define is_array0_correct (array[0] == 0)
#define is_array1_correct (array[1] == 1)
#define is_array2_correct (array[2] == 2)
#define is_array3_correct (array[3] == 3)
#define is_i_valid (i >= 0 && i <= 4)
#define is_array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_i { [] is_i_valid }
ltl all_elements_correct { <> is_array_correct }
ltl array0_correct_always { [] is_array0_correct }
ltl array1_correct_eventually { <>[] is_array1_correct }
ltl array0_then_array1 { [] (is_array0_correct -> <> is_array1_correct) }
ltl array1_then_array2 { [] (is_array1_correct -> <> is_array2_correct) }
ltl array2_then_array3 { [] (is_array2_correct -> <> is_array3_correct) }
ltl array1_correct_always { [] (is_array1_correct -> [] is_array1_correct) }
ltl array1_correct_until_array2 { [] (is_array1_correct -> (is_array1_correct U is_array2_correct)) }
int array[4];
int i = 0;
active proctype test(){
	do
	:: i < 4;
		array[i] = i;
		array[1]++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
