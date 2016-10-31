package body Complex_Arrays
is
   pragma Warnings (Off, "* has no effect");

   type    Counter is range 0 .. 1002;
   subtype Index   is Counter range 0 .. 1001;
   type    Value   is range -23 .. 69;

   type Basic_Array is array (Index) of Value;

   type Basic_Record is record
      Flag         : Boolean;
      First_Value  : Value;
      Second_Value : Value;
   end record;

   type Array_Of_Arrays is array (Index) of Basic_Array;


   -- Arrays of Arrays --

   procedure AA_Element_Access (A    : in Array_Of_Arrays;
                                I, J : in Index;
                                V    : in Value)
     with Depends => (null => (A, I, J, V)),
          Post    => A(I)(J) = V  --  @POSTCONDITION:FAIL
   is
   begin
      null;
   end AA_Element_Access;

   procedure AA_Array_Access (A    : in Array_Of_Arrays;
                              I, J : in Index)
     with Depends => (null => (A, I, J)),
          Post    => A(I) = A(J)  --  @POSTCONDITION:FAIL
   is
   begin
      null;
   end AA_Array_Access;


   procedure AA_Element_Update_And_Access (A    : in out Array_Of_Arrays;
                                           I, J : in     Index;
                                           V    : in     Value)
     with Depends => (A =>+ (I, J, V)),
          Post    => A(I)(J) = 17  --  @POSTCONDITION:FAIL
   is
   begin
      A(I)(J) := V;
   end AA_Element_Update_And_Access;

   procedure AA_Array_Update_And_Access (A : in out Array_Of_Arrays;
                                         I : in     Index)
     with Depends => (A =>+ I),
          Post    => A(I) = A(23)  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := A(17);
   end AA_Array_Update_And_Access;


   procedure AA_Element_Overwrite (A    : in out Array_Of_Arrays;
                                   I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Post    => A(I)(J) = A(J)(I)  --  @POSTCONDITION:FAIL
   is
   begin
      A(I)(J) := A(J)(I);
      A(I)(J) := A(0)(1);
   end AA_Element_Overwrite;

   procedure AA_Array_Overwrite (A    : in out Array_Of_Arrays;
                                 I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Post    => A(I) = A(J)  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := A(J);
      A(I) := A(0);
   end AA_Array_Overwrite;


   procedure AA_Element_Passthrough (A    : in out Array_Of_Arrays;
                                     I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A(I)(J) /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(I)(J) := 23;
      A(J)(I) := 42;
   end AA_Element_Passthrough;


   procedure AA_Array_Passthrough (A    : in out Array_Of_Arrays;
                                   I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A(I) /= A(23)  --  @POSTCONDITION:FAIL
   is
   begin
      A(I) := A(23);
      A(J) := A(42);
   end AA_Array_Passthrough;



   procedure AA_Element_Swap (A    : in out Array_Of_Arrays;
                              I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp     := A(I)(J);
      A(I)(J) := A(J)(I);
      A(J)(I) := Tmp;
   end AA_Element_Swap;


   procedure AA_Array_Swap (A    : in out Array_Of_Arrays;
                            I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Basic_Array;
   begin
      Tmp  := A(I);
      A(I) := A(J);
      A(J) := Tmp;
   end AA_Array_Swap;





   -- Functions that return arrays --

   function Create_Step_Array (I : in Index) return Basic_Array
     with Post => (for all J in Index =>  --  @POSTCONDITION:PASS
                     (if J < I  then
                        Create_Step_Array'Result (J) = Value'First) and
                     (if J >= I then
                        Create_Step_Array'Result (J) = Value'Last))
   is
      Tmp : Basic_Array;
   begin
      Tmp := Basic_Array'(others => 0);

      for J in Index range Index'First .. I loop
         Tmp(J) := Value'First;
         pragma Loop_Invariant
           ((for all K in Index range Index'First..J =>  --  @LOOP_INVARIANT_INIT:PASS  @LOOP_INVARIANT_PRESERV:PASS
               (if K <= J then Tmp (K) = Value'First))
            and I = I'Loop_Entry);
      end loop;

      for J in Index range I .. Index'Last loop
         Tmp(J) := Value'Last;
         pragma Loop_Invariant
           (for all K in Index range Index'First..J =>  --  @LOOP_INVARIANT_INIT:PASS  @LOOP_INVARIANT_PRESERV:PASS
              (if K < I  then Tmp (K) = Value'First) and
              (if K >= I then Tmp (K) = Value'Last));
      end loop;

      return Tmp;
   end Create_Step_Array;

   function Use_Step_Array (I : Index) return Counter
     with Post => I = Use_Step_Array'Result  --  @POSTCONDITION:PASS
   is
      Step : Basic_Array;
      C    : Counter := 0;
   begin
      Step := Create_Step_Array(I);

      for J in Index loop
         if Step(J) = Value'First then
            C := C + 1;
         end if;

         pragma Loop_Invariant
           ((for all K in Index =>  --  @LOOP_INVARIANT_INIT:PASS  @LOOP_INVARIANT_PRESERV:PASS
               (if K < I  then Step (K) = Value'First) and
               (if K >= I then Step (K) = Value'Last))
            and (if J < I  then C = J + 1)
            and (if J >= I then C = I));

      end loop;

      return C;
   end Use_Step_Array;

   pragma Warnings (On, "* has no effect");
end Complex_Arrays;
