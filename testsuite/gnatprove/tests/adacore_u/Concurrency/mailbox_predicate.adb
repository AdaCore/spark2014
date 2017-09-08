package body Mailbox_Predicate
  with SPARK_Mode
is
   protected body Mailbox is
      entry Publish when C.Not_Full is
         Not_Full     : Boolean := C.Not_Full;
         Num_Messages : Natural := C.Num_Messages;
      begin
         Num_Messages := Num_Messages + 1;
         if Num_Messages = Max then
            Not_Full := False;
         end if;
         C := (True, Not_Full, Num_Messages);
      end Publish;

      entry Retrieve when C.Not_Empty is
         Not_Empty    : Boolean := C.Not_Empty;
         Num_Messages : Natural := C.Num_Messages;
      begin
         Num_Messages := Num_Messages - 1;
         if Num_Messages = 0 then
            Not_Empty := False;
         end if;
         C := (Not_Empty, True, Num_Messages);
      end Retrieve;
   end Mailbox;

end Mailbox_Predicate;
