
package body Patience
  with SPARK_Mode
is

   procedure PlayCard (C:in Card; S: in out State) is
      Idx, Pred, I : Integer;
      StackISize, TopStackI : CardIndex;
   begin
      Pred := -1;
      I := 0;
      while I < S.NumStacks loop
         pragma Loop_Invariant (I in 0 .. S.NumStacks);
         pragma Loop_Invariant
           (
            (if I = 0 then Pred = -1 else
           -- let stack_im1 = s.stacks[i-1] in
           -- let stack_im1_size = s.stack_sizes[i-1] in
           -- let top_stack_im1 = stack_im1[stack_im1_size - 1] in
           (Pred in 0 .. S.NumElts - 1
              and then
              Pred = S.Stacks(I-1)(S.StackSizes(I-1)-1)
            and then
              C > S.Values(Pred)
              and then
              -- let (ps,_pp) = s.positions[!pred] in
              S.PosStack(Pred) = I-1
           )));
           StackISize := S.StackSizes(I);
           TopStackI := S.Stacks(I)(StackISize - 1);
           exit when C <= S.Values(TopStackI);
           pragma Assert (0 <= TopStackI and TopStackI < S.Numelts);
           pragma Assert
             (-- let (is,ip) = s.positions[top_stack_i] in
              0 <= S.PosStack(TopStackI) and then
                S.PosStack(TopStackI) < S.NumStacks and then
                0 <= S.PosHeight(TopStackI) and then
                 S.PosHeight(TopStackI) < S.StackSizes(S.PosStack(TopStackI)) and then
                 S.Stacks(S.PosStack(TopStackI))( S.PosHeight(TopStackI)) = TopStackI and then
                S.PosStack(TopStackI) = I and then S.PosHeight(TopStackI) = StackISize - 1
             );
           Pred := TopStackI;
           I := I + 1;
            end loop;
      Idx := S.NumElts;
      S.Values(Idx) := C;
      S.NumElts := Idx + 1;
      S.Preds(Idx) := Pred;
      if I = S.NumStacks then
         -- we add a new stack
         begin
            I := S.NumStacks;
            S.NumStacks := S.NumStacks + 1;
            S.StackSizes(I) := 1;
            S.Stacks(I)(0) := Idx;
            S.PosStack(Idx) := I;
            S.PosHeight(Idx) := 0;
         end;
      else
         -- we put c on top of stack i
         begin
            StackISize := S.StackSizes(I);
            S.StackSizes(I) := StackISize + 1;
            S.Stacks(I)(StackISize) := Idx;
            S.PosStack(Idx) := I;
            S.PosHeight(Idx) := StackISize;
         end;
      end if;

      pragma Assert
      (0 <= S.NumStacks and then
         S.NumStacks <= S.NumElts
         -- the number of stacks is less or equal the number of cards
         and then S.NumElts <= MaxNumCards
         and then
         (S.NumElts = 0 or else S.NumStacks > 0)
         -- when there is at least one card, there is at least one stack
         );
      pragma Assert (for all I in 0 .. S.NumStacks - 1 =>
            S.StackSizes(I) >= 1);
            -- stacks are non-empty
      pragma Assert (for all I in 0 .. S.NumStacks - 1 =>
            S.StackSizes(I) <= S.NumElts
            -- stack sizes are at most the number of cards
            and
            (for all J in 0 .. S.StackSizes(I) - 1 =>
               0 <= S.Stacks(I)(J) and S.Stacks(I)(J) < S.NumElts)
            -- contents of stacks are valid card indexes
         );
      pragma Assert (
         (for all I in 0 .. S.NumElts -1 =>
            S.PosStack(I) in 0 .. S.NumStacks - 1
            and then
            S.PosHeight(I) in 0 .. S.StackSizes(S.PosStack(I)) - 1
            and then S.Stacks(S.PosStack(I))(S.PosHeight(I)) = I)
         -- the position table of cards is correct, i.e. card I indeed
         -- occurs in stack S.PosStack(I) at height S.PosHeight(I)
         and then
         (for all IST in 0 .. S.NumStacks - 1 =>
          (for all IP in 0 .. S.StackSizes(IST) - 1 =>
             IST = S.PosStack(S.Stacks(IST)(IP))
             and
             IP = S.PosHeight(S.Stacks(IST)(IP))))
         -- positions is the proper inverse of stacks
         and then
         (for all I in 0 .. S.NumStacks -1 =>
            (for all J in 0 .. S.StackSizes(I) - 2 =>
               (for all K in J+1 .. S.StackSizes(I) - 1 =>
                  S.Stacks(I)(J) < S.Stacks(I)(K))))
         -- in a given stack, indexes are increasing from bottom to top
         and then
         (for all I in 0 .. S.NumStacks - 1 =>
            (for all J in 0 .. S.StackSizes(I) - 2 =>
               (for all K in J+1 .. S.StackSizes(I) - 1 =>
                  S.Values(S.Stacks(I)(J)) >= S.Values(S.Stacks(I)(K)))))
         -- in a given stack, card values are decreasing from bottom to top
         and then
         (for all I in 0 .. S.NumElts - 1 =>
            S.Preds(I) in -1 .. S.NumElts - 1
            -- the predecessor is a valid index or -1
            and then
            S.Preds(I) < I
            -- predecessor is always a smaller index
            and then
            (if S.Preds(I) < 0 then S.PosStack(I) = 0
        -- if predecessor is -1 then I is in leftmost stack
            else
            (S.Values(S.Preds(I)) < S.Values(I)
          -- if predecessor is not -1, it denotes a card with smaller value...
          and then S.PosStack(I) > 0
          -- ...the card is not on the leftmost stack...
          and then S.PosStack(S.Preds(I)) = S.PosStack(I) - 1)
          -- ...and predecessor is in the stack on the immediate left
            )
          ));

   end;



   function PlayGame (Cards: CardStack) return State
   is
      S : State := Null_State;
   begin
      for I in Cards'Range loop
         pragma Loop_Invariant (S.NumElts = I - Cards'First);
         pragma Loop_Invariant (Inv(S));
         PlayCard(Cards(I),S);
      end loop;
      return S;
   end PlayGame;

end Patience;
