#define valid_index (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
#define index_complete (i == 4)
#define array_0_correct (array[0] == 0)
#define array_1_correct (array[1] == 1)
#define array_2_correct (array[2] == 2)
#define array_3_correct (array[3] == 3)
ltl valid_index_always { [] valid_index }
ltl eventually_array_correct { <> array_correct }
ltl eventually_index_complete { <> index_complete }
ltl array_correct_when_index_complete { [] (index_complete -> array_correct) }
ltl array_0_correct_always { [] array_0_correct }
ltl array_1_correct_remains { [] (array_1_correct -> [] array_1_correct) }
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
