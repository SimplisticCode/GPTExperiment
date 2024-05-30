#define array0_correct (array[0] == 0)
#define array1_correct (array[1] == 1)
#define array2_correct (array[2] == 2)
#define array3_correct (array[3] == 3)
#define index_valid (i >= 0 && i <= 4)
ltl valid_index { [] index_valid }
ltl eventually_array0_correct { <> array0_correct }
ltl eventually_array1_correct { <> array1_correct }
ltl eventually_array2_correct { <> array2_correct }
ltl eventually_array3_correct { <> array3_correct }
ltl array_correct { [] (i == 4 -> (array0_correct && array1_correct && array2_correct && array3_correct)) }
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
