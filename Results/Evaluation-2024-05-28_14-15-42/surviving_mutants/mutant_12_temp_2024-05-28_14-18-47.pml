#define is_turn_A (turn == false)
#define is_turn_B (turn == true)
#define flag_A (flag[0] == true)
#define flag_B (flag[1] == true)
#define cnt_0 (cnt == 0)
#define cnt_1 (cnt == 1)
ltl valid_cnt { [](cnt_0 || cnt_1) }
ltl valid_flags { []((flag[0] == true || flag[0] == false) && (flag[1] == true || flag[1] == false)) }
ltl valid_turn { []((turn == true || turn == false)) }
ltl progress_A { [](flag_A -> <> cnt_1) }
ltl progress_B { [](flag_B -> <> cnt_1) }
ltl turn_taking { [](flag_A && is_turn_A -> <> is_turn_B) && [](flag_B && is_turn_B -> <> is_turn_A) }
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
	:: false;
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
