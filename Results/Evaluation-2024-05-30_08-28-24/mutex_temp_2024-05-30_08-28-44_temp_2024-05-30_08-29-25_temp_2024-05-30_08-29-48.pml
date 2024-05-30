#define in_critical_A (cnt == 1 && turn == false)
#define in_critical_B (cnt == 1 && turn == true)
#define wants_A (flag[0] == true)
#define wants_B (flag[1] == true)
#define exited_A (cnt == 0 && turn == true && flag[0] == false)
#define exited_B (cnt == 0 && turn == false && flag[1] == false)
ltl valid_cnt { [](cnt == 0 || cnt == 1) }
ltl mutual_exclusion { [](in_critical_A -> !in_critical_B) && [](in_critical_B -> !in_critical_A) }
ltl progress_A { [](wants_A -> <> in_critical_A) }
ltl progress_B { [](wants_B -> <> in_critical_B) }
ltl flag_reset_A { [](in_critical_A -> <> exited_A) }
ltl flag_reset_B { [](in_critical_B -> <> exited_B) }
ltl immediate_flag_reset_A { [](in_critical_A -> <> (cnt == 0 && flag[0] == false)) }
ltl immediate_flag_reset_B { [](in_critical_B -> <> (cnt == 0 && flag[1] == false)) }
ltl turn_alternation { [](in_critical_A -> <> (cnt == 0 && turn == true)) && [](in_critical_B -> <> (cnt == 0 && turn == false)) }
bool turn;
bool flag[2];
byte cnt;

active proctype ProcessA()
{
    int i = 0; // Assuming process A has a fixed id of 0
    int j = 1;
    do
    :: true -> // Replaces the againA label for repetition
        flag[i] = true;
        do
        :: flag[j] ->
            if
            :: turn == j ->
                flag[i] = false;
                !(turn == j);
                flag[i] = true
            :: else
            fi
        :: else ->
            break
        od;

        cnt++;
        assert(cnt == 1); /* critical section */
        cnt--;

        turn = j;
        flag[i] = false;
    od; // End of outer loop for continuous execution
}

active proctype ProcessB()
{
    int i = 1; // Assuming process B has a fixed id of 1
    int j = 0;
    do
    :: true -> // Replaces the againB label for repetition
        flag[i] = true;
        do
        :: flag[j] ->
            if
            :: turn == j ->
                flag[i] = false;
                !(turn == j);
                flag[i] = true
            :: else
            fi
        :: else ->
            break
        od;

        cnt++;
        assert(cnt == 1); /* critical section */
        cnt--;

        turn = j;
        flag[i] = false;
    od; // End of outer loop for continuous execution
}