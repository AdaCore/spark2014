package Mailbox_Predicate
  with SPARK_Mode
is
   Max : constant := 100;

   type Content is record
      Not_Empty    : Boolean := False;
      Not_Full     : Boolean := True;
      Num_Messages : Natural := 0;
   end record
     with Predicate => Num_Messages in 0 .. Max
                   and Not_Empty = (Num_Messages > 0)
                   and Not_Full = (Num_Messages < Max);

   protected type Mailbox is
      entry Publish;
      entry Retrieve;
   private
      C : Content;
   end Mailbox;

end Mailbox_Predicate;
