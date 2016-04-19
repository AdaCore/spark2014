package Ghost_Example is

   procedure Init (Done : out Boolean) with
     Pre  => Cur_State = Start,
     Post => Cur_State = (if Done then Init_Done else Start);

   procedure First_Work_Item (Done : out Boolean) with
     Pre  => Cur_State = Init_Done,
     Post => Cur_State = (if Done then In_Progress else Init_Done);

   procedure Second_Work_Item (Done : out Boolean) with
     Pre  => Cur_State = In_Progress,
     Post => Cur_State = (if Done then All_Done else In_Progress);

   procedure Reset with Ghost,
     Post => Cur_State = Start;

   type State_T is (Start, Init_Done, In_Progress, All_Done);
   function Cur_State return State_T with Ghost;

private

   State : State_T := Start with Ghost;
   function Cur_State return State_T is (State);

end Ghost_Example;
