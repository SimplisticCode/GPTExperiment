#define valid_i (i >= 0 && i <= 4)
#define array_0_correct (array[0] == 0)
#define array_1_correct (array[1] == 1)
#define array_2_correct (array[2] == 2)
#define array_3_correct (array[3] == 3)
ltl valid_i_range { [] valid_i }
ltl eventually_array_0_correct { <> array_0_correct }
ltl eventually_array_1_correct { <> array_1_correct }
ltl eventually_array_2_correct { <> array_2_correct }
ltl eventually_array_3_correct { <> array_3_correct }
ltl final_assertion { [] (i == 4 -> (array_0_correct && array_1_correct && array_2_correct && array_3_correct)) }
int array[4];
int i = 0;
active proctype test(){
	do
	:: i < 5;
		array[i] = i;
		i++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
