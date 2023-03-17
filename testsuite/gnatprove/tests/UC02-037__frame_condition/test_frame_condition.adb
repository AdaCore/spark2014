procedure Test_Frame_Condition with SPARK_Mode is

   --  Test that handlers are taken into account in the frame condition
   --  computation.

   Process_Error : exception;

   procedure Process (X : in out Integer) with
     Exceptional_Cases => (Process_Error => True);

   procedure Process (X : in out Integer) is
   begin
      if X = Integer'Last then
         raise Process_Error;
      end if;
      X := X + 1;
   end Process;

   type Int_Array is array (Positive range <>) of Integer;
   type Bool_Array is array (Positive range <>) of Boolean;

   --  Test that the generated frame condition is precise enough in simple cases

   procedure Process_All (A : in out Int_Array; Status : in out Bool_Array) with
     Pre  => A'First = Status'First and A'Last = Status'Last,
     Post => (for all I in A'Range => (if Status (I) then A (I) = A'Old (I)))
     and (for all I in A'Range => (if Status'Old (I) then Status (I)));

   procedure Process_All (A : in out Int_Array; Status : in out Bool_Array) is
   begin
      for I in A'Range loop
         begin
            if not Status (I) then
               Process (A (I));
            end if;
         exception
            when Process_Error =>
               Status (I) := True;
         end;
         pragma Loop_Invariant
           (for all K in A'First .. I =>
              (if Status'Loop_Entry (K) then Status (K)));
         pragma Loop_Invariant
           (for all K in A'First .. I =>
              (if Status (K) then A (K) = A'Loop_Entry (K)));
      end loop;
   end Process_All;

   --  Test that handlers are not ignored

   procedure Process_All_Bad (A : in out Int_Array; Status : in out Bool_Array) with
     Pre  => A'First = Status'First and A'Last = Status'Last,
     Post => Status'Old = Status; --@POSTCONDITION:FAIL

   procedure Process_All_Bad (A : in out Int_Array; Status : in out Bool_Array) is
   begin
      for I in A'Range loop
         begin
            if not Status (I) then
               Process (A (I));
            end if;
         exception
            when Process_Error =>
               Status (I) := True;
         end;
         pragma Loop_Invariant
           (for all K in A'First .. I =>
              (if Status'Loop_Entry (K) then Status (K)));
         pragma Loop_Invariant
           (for all K in A'First .. I =>
              (if Status (K) then A (K) = A'Loop_Entry (K)));
      end loop;
   end Process_All_Bad;
begin
   null;
end Test_Frame_Condition;
