procedure Struct_Decrease_Transfer_Of_Control with SPARK_Mode is
   type Cell;
   type ACell is access Cell;
   type Cell is record
      Head : Integer;
      Tail : ACell;
   end record;
   function Rand (X : Integer) return Boolean with Global => null, Import;
   E : exception;
   procedure Raise_Exception
     with
       Global => null,
       Exceptional_Cases => (E => True);
   procedure Raise_Exception is
   begin
      raise E;
   end Raise_Exception;
   procedure Test_Exception_1 (X : ACell) is
      Y : access Cell := X;
   begin
      while Y /= null loop
         pragma Loop_Variant (Structural => Y); --@LOOP_VARIANT:FAIL
         begin
            Y := Y.Tail;
            Raise_Exception;
         exception
            when E =>
               if Y /= null then
                  Y.Tail := new Cell'(Head => 0, Tail => null);
               end if;
         end;
      end loop;
   end Test_Exception_1;
   procedure Test_Exception_2 (X : ACell) is
      Y : access Cell := X;
   begin
      while Y /= null loop
         pragma Loop_Variant (Structural => Y);
         begin
            raise E;
         exception
            when E => Y := Y.Tail;
         end;
      end loop;
   end Test_Exception_2;
   function Test_Extended_Return (X : ACell) return Boolean is
      Y : access constant Cell := X;
   begin
      while Y /= null loop
         pragma Loop_Variant (Structural => Y); --@LOOP_VARIANT:FAIL
         begin
            return X : Boolean := True do
               Raise_Exception;
            end return;
         exception
            when E => null;
         end;
      end loop;
      return False;
   end Test_Extended_Return;
   procedure Test_Goto (X : ACell) is
      Y : access constant Cell := X;
   begin
      while Y /= null loop
         pragma Loop_Variant (Structural => Y);
         if Rand (Y.Head) then
            Y := Y.Tail;
            goto A;
         else
            goto B;
         end if;
         <<B>>
         Y := Y.Tail;
         <<A>>
      end loop;
   end;
begin
   null;
end Struct_Decrease_Transfer_Of_Control;
