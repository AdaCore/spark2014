procedure Test_Relaxed with SPARK_Mode is

   procedure Test_Int (B : Boolean) is
      type R is new Integer with Relaxed_Initialization;
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
      function Constant_Reference (C : Container; I : Natural) return
      not null access constant R is
        (C.Content (I))
          with Pre => Has_Element (C, I);

      procedure Test (C : Container) is
      begin
         if B then
            for E of C loop
               if E /= 1 then  --  @INIT_BY_PROOF:FAIL
                  null;
               end if;
            end loop;
         else
            pragma Assert (for all E of C => E'Initialized); --  @ASSERT:FAIL
         end if;
      end;
   begin
      null;
   end;

   procedure Test_Record (B : Boolean) is
      type R is record
         F : Integer;
      end record with Relaxed_Initialization;
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
      function Constant_Reference (C : Container; I : Natural) return
      not null access constant R is
        (C.Content (I))
          with Pre => Has_Element (C, I);

      V : R;
      C : Container := (Max => 5, Content => (1 .. 5 => new R'(V)));
   begin
      if B then
         for E of C loop
            if E.F /= 1 then  --  @INIT_BY_PROOF:FAIL
               null;
            end if;
         end loop;
      else
         pragma Assert (for all E of C => E'Initialized); --  @ASSERT:FAIL
      end if;
   end;
begin
   null;
end;
