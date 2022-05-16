function Palindrom (Str : String) return Boolean
with
  SPARK_Mode => On,
  Pre => Str /= ""
is
    Length : Integer := Str'Length;
    I : Integer := Str'First;
    J : Integer := Str'Last;
    Stop : constant Integer := I + (Length - 1) / 2;
begin
    while I <= Stop and Str(I) = Str(J) loop
       I := I + 1;
       J := J - 1;
       pragma Loop_Invariant (I in I'Loop_Entry .. Stop);
       pragma Loop_Invariant (J in Stop .. J'Loop_Entry);
       pragma Loop_Invariant (I - I'Loop_entry = J'Loop_entry - J);
    end loop;

    return I = Stop;
end Palindrom;
