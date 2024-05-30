#define is_turn_A (turn == false)
#define is_turn_B (turn == true)
#define flag_A (flag[0] == true)
#define flag_B (flag[1] == true)
#define cnt_zero (cnt == 0)
#define cnt_one (cnt == 1)
ltl valid_cnt { [](cnt_zero || cnt_one) }
ltl mutual_exclusion { [](cnt <= 1) }
ltl progress_A { [](flag_A -> <> cnt_one) }
ltl progress_B { [](flag_B -> <> cnt_one) }
ltl alternation_A { [](flag_A -> (is_turn_A U is_turn_B)) }
ltl alternation_B { [](flag_B -> (is_turn_B U is_turn_A)) }
bool turn;
bool flag[2];
byte cnt;
active proctype ProcessA(){
	int i = 0;
	int j = 1;
	do
	:: true;
		flag[i] = true;
		do
		:: flag[j];
			if
			:: turn == j;
				flag[i] = false;
				!(turn == j);
				flag[i] = true;
			:: else;
			fi;
		:: else;
			break;
		od;
		cnt++;
		assert(cnt == 1);
		cnt--;
		turn = j;
		flag[i] = false;
	od;
}
active proctype ProcessB(){
	int i = 1;
	int j = 0;
	do
	:: true;
		flag[i] = true;
		do
		:: flag[j];
			if
			:: turn == j;
				flag[i] = false;
				!(turn > j);
				flag[i] = true;
			:: else;
			fi;
		:: else;
			break;
		od;
		cnt++;
		assert(cnt == 1);
		cnt--;
		turn = j;
		flag[i] = false;
	od;
}
