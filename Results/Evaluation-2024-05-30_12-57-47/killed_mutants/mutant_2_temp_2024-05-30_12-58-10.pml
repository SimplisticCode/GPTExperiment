#define i_in_range (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_i_range { [] i_in_range }
ltl eventually_i_4 { <> (i == 4) }
ltl eventually_array_correct { <> array_correct }
ltl array_correct_when_i_4 { [] (i == 4 -> array_correct) }
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
