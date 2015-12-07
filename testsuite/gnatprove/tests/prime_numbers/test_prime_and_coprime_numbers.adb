with Prime_And_Coprime_Numbers;

procedure Test_Prime_And_Coprime_Numbers
   with SPARK_Mode
is
   package P is new Prime_And_Coprime_Numbers (Value_Type => Natural,
                                               Max_Value  => 100_000);

   Coprimes : P.Number_List_Type;
   Result : Positive;
begin
   Result := P.Nearest_Prime_Number (555, P.Down);
   Coprimes := P.Initialize_Coprime_List (2000);
   Result := P.Nearest_Number (Coprimes, P.Down, 555);
end Test_Prime_And_Coprime_Numbers;
