pragma Extensions_Allowed (All_Extensions);

procedure Test with SPARK_Mode is
   type Arr is array (1 .. 2) of Integer;

   function Capture_Array
     (Before_1, Before_2 : Integer;
      After_1, After_2   : Integer) return Arr
   with
     Depends =>
       (Capture_Array'Result => (Before_1, Before_2),
        null                 => (After_1, After_2));

   function Capture_Array
     (Before_1, Before_2 : Integer;
      After_1, After_2   : Integer) return Arr
   is
      A : Arr := (Before_1, Before_2);
   begin
      <<Capture>>
      A := (After_1, After_2);
      return A'At (Capture);
   end Capture_Array;

begin
   null;
end Test;
