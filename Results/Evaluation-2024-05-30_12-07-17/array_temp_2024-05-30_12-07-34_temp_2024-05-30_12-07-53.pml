#define i_in_range (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_i { [] i_in_range }
ltl eventually_correct_array { <> array_correct }
ltl eventually_i_4 { <> (i == 4) }
ltl correct_array_0 { [] (i == 0 -> array[0] == 0) }
ltl correct_array_1 { [] (i == 1 -> array[1] == 1) }
ltl correct_array_2 { [] (i == 2 -> array[2] == 2) }
ltl correct_array_3 { [] (i == 3 -> array[3] == 3) }
ltl array_0_stable { [] (array[0] == 0 -> X array[0] == 0) }
ltl array_1_stable { [] (array[1] == 1 -> X array[1] == 1) }
ltl array_2_stable { [] (array[2] == 2 -> X array[2] == 2) }
ltl array_3_stable { [] (array[3] == 3 -> X array[3] == 3) }
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