#define valid_i (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_index { [] valid_i }
ltl eventually_i_4 { <> (i == 4) }
ltl array_correct_before_end { [] (i == 4 -> array_correct) }
ltl eventually_array_correct { <> array_correct }
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
