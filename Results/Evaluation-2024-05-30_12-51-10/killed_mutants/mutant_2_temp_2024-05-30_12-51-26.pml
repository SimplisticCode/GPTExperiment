#define valid_i (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_index { [] valid_i }
ltl eventually_correct_array_0 { <> (array[0] == 0) }
ltl eventually_correct_array_1 { <> (array[1] == 1) }
ltl eventually_correct_array_2 { <> (array[2] == 2) }
ltl eventually_correct_array_3 { <> (array[3] == 3) }
ltl final_assertion { [] (i == 4 -> array_correct) }
int array[4];
int i = 0;
active proctype test(){
	do
	:: i >= 4;
		array[i] = i;
		i++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
