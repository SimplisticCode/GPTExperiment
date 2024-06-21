#define i_in_range (i >= 0 && i <= 4)
#define array_set_correctly (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_i_range { [] i_in_range }
ltl eventually_array_set_correctly { <> array_set_correctly }
ltl i_stops_at_4 { [] (i == 4 -> [] (i == 4)) }
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
}
