--  PantherChess - based on AdaChess Copyright (C) 2017-2018 Bill Zuercher

with ACChessBoard; use ACChessBoard;


package ACPonder is


   task type Thinking_Task_Type is
      entry Start (Move : Move_Type);
--      entry Stop;
   end Thinking_Task_Type;

   type Thinking_Task_Access_Type is access Thinking_Task_Type;

   procedure Start_Ponder (Move : Move_Type);
   procedure Stop_Ponder;

   -----------------
   -- Ponder Mode --
   -----------------

   type Ponder_Mode_Type is (On, Off);

   Ponder_Mode : Ponder_Mode_Type := On;


   -----------------
   -- Ponder data --
   -----------------

   Ponder_Move : Move_Type;

private

   Brain : Thinking_Task_Access_Type := null;
   Ponder_Stopped : Boolean := True;

end ACPonder;
