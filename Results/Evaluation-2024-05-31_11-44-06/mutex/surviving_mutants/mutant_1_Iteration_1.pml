#define turn_is_true (turn == true)
#define turn_is_false (turn == false)
#define flag0_true (flag[0] == true)
#define flag0_false (flag[0] == false)
#define flag1_true (flag[1] == true)
#define flag1_false (flag[1] == false)
#define cnt_zero (cnt == 0)
#define cnt_one (cnt == 1)
ltl valid_turn { [] (turn_is_true || turn_is_false) }
ltl valid_flag0 { [] (flag0_true || flag0_false) }
ltl valid_flag1 { [] (flag1_true || flag1_false) }
ltl mutual_exclusion { [] (cnt_zero || cnt_one) }
ltl progress_A { [] (flag0_true -> <> cnt_one) }
ltl progress_B { [] (flag1_true -> <> cnt_one) }
bool turn;
bool flag[2];
byte cnt;
active proctype ProcessA(){
	int i = 0;
	int j = 1;
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
