#define array_0_correct (array[0] == 0)
#define array_1_correct (array[1] == 1)
#define array_2_correct (array[2] == 2)
#define array_3_correct (array[3] == 3)
#define index_reached_end (i == 4)
#define index_0 (i == 0)
#define index_1 (i == 1)
#define index_2 (i == 2)
#define index_3 (i == 3)
ltl eventually_array_0_correct { <> array_0_correct }
ltl eventually_array_1_correct { <> array_1_correct }
ltl eventually_array_2_correct { <> array_2_correct }
ltl eventually_array_3_correct { <> array_3_correct }
ltl eventually_index_reached_end { <> index_reached_end }
ltl array_correct_at_end { [] (index_reached_end -> (array_0_correct && array_1_correct && array_2_correct && array_3_correct)) }
ltl array_0_correct_when_index_1 { [] (index_1 -> array_0_correct) }
ltl array_1_correct_when_index_2 { [] (index_2 -> (array_0_correct && array_1_correct)) }
ltl array_2_correct_when_index_3 { [] (index_3 -> (array_0_correct && array_1_correct && array_2_correct)) }
ltl array_3_correct_when_index_4 { [] (index_reached_end -> (array_0_correct && array_1_correct && array_2_correct && array_3_correct)) }
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