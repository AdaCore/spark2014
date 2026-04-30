package body Hashtbl
  with SPARK_Mode
is

   function Mem (T : Table; Key : Data) return Boolean is
      H    : constant U32 := Hash (Key, U32 (T.Cells'Length));
      Buck : access constant Cell_Rec := T.Cells (H);
   begin
      while Buck /= null loop
         pragma Loop_Variant (Structural => Buck);
         pragma Loop_Invariant
           (M.FS.Contains (M.Model (T.Cells (H)), Key) =
              M.FS.Contains (M.Model (Buck), Key));
         if Buck.D = Key then
            return True;
         end if;
         Buck := Buck.Next;
      end loop;
      return False;
   end Mem;

   function At_End_Borrow
     (E : access constant Cell_Rec) return access constant Cell_Rec
   is (E)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   procedure Insert (T : in out Table; Key : Data; Success : out Boolean) is
      Modulus : constant U32 := U32 (T.Cells'Length);
      H       : constant U32 := Hash (Key, Modulus);
   begin
      if T.Cells (H) = null then
         T.Cells (H) := new Cell_Rec'(D => Key, Next => null);
         pragma Assert
           (M.FS.Contains (M.Model (T.Cells (H)), Key));
         T.Size := T.Size + 1;
         Success := True;
         return;
      end if;
      declare
         Buck : access Cell_Rec := T.Cells (H);
      begin
         loop
            pragma Loop_Invariant (Buck /= null);
            pragma Loop_Invariant (Has_Hash (Buck, H, Modulus));
            pragma Loop_Invariant
              ((if Has_Hash (At_End_Borrow (Buck), H, Modulus)
                then Has_Hash (At_End_Borrow (T.Cells (H)), H, Modulus)));
            pragma Loop_Invariant
              ((if M.FS.Contains (M.Model (At_End_Borrow (Buck)), Key)
                then M.FS.Contains
                  (M.Model (At_End_Borrow (T.Cells (H))), Key)));
            pragma Loop_Variant (Structural => Buck);
            if Buck.D = Key then
               Success := False;
               return;
            end if;
            if Buck.Next = null then
               Buck.Next := new Cell_Rec'(D => Key, Next => null);
               Success := True;
               exit;
            else
               Buck := Buck.Next;
            end if;
         end loop;
      end;
      pragma Assert
        (M.FS.Contains (M.Model (T.Cells (H)), Key));
      if Success then
         T.Size := T.Size + 1;
      end if;
   end Insert;

end Hashtbl;
