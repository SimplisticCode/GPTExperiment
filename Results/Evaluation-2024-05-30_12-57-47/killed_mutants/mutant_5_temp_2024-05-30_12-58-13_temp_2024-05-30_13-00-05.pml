#define array_0_correct (array[0] == 0)
#define array_1_correct (array[1] == 1)
#define array_2_correct (array[2] == 2)
#define array_3_correct (array[3] == 3)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl eventually_i_4 { <> (i == 4) }
ltl eventually_array_correct { <> array_correct }
ltl array_correct_when_i_4 { [] (i == 4 -> array_correct) }
ltl array_0_correct_when_i_1 { [] (i == 1 -> array_0_correct) }
ltl array_1_correct_when_i_2 { [] (i == 2 -> array_1_correct) }
ltl array_2_correct_when_i_3 { [] (i == 3 -> array_2_correct) }
ltl array_3_correct_when_i_4 { [] (i == 4 -> array_3_correct) }
ltl array_1_not_incremented { [](array_1_correct -> [] array_1_correct) }
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
