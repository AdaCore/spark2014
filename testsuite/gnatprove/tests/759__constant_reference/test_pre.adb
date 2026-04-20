procedure Test_Pre with SPARK_Mode is
   type R is record
      F : Integer;
   end record;
   type R_Acc is access R;
   type Data_Array is array (Positive range <>) of not null R_Acc;
   type Container (Max : Natural) is record
      Content : Data_Array (1 .. Max);
   end record with
     Iterable =>
       (First => First,
        Next => Next,
        Has_Element => Has_Element,
        Constant_Reference => Constant_Reference);

   function First (C : Container) return Natural is (1);
   function Next (C : Container; I : Natural) return Natural is
     (if I in 1 .. C.Max - 1 then I + 1 else 0);
   function Has_Element (C : Container; I : Natural) return Boolean is
     (I in 1 .. C.Max);
   function Pre (C : Container; I : Natural) return Boolean with Import, Global => null;
   function Constant_Reference (C : Container; I : Natural) return --  @PRECONDITION:FAIL
   not null access constant R is
     (C.Content (I))
   with Pre => Pre (C, I) and Has_Element (C, I);

   C : Container := (Max => 5, Content => (1 .. 5 => new R'(F => 1)));
begin
   for E of C loop --  @PRECONDITION:FAIL
      if E.F /= 1 then
         raise Program_Error;
      end if;
   end loop;

   pragma Assert (for all E of C => E.F = 1);
end;
