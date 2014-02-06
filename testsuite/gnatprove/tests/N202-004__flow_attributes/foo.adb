package body Foo
is

   procedure Test_01_Ok (A : in String;
                         B : out Natural)
   with Depends => (B => A)
   is
   begin
      B := A'Length;
   end Test_01_Ok;

   procedure Test_02_Ok (A : in String;
                         B : out Natural)
   with Depends => (B => A)
   is
      Tmp : String := A & "foo";

      procedure P (X : out Natural)
      with Global => Tmp,
           Depends => (X => Tmp)
      is
      begin
         X := Tmp'Length;
      end P;

   begin
      P (B);
   end Test_02_Ok;

   procedure Test_03_Ok (A : in out String;
                         B : out Natural)
   with Depends => ((A, B) => A)
   is
   begin
      A (A'First) := ' ';
      B := A'Length;
   end Test_03_Ok;

   procedure Test_04_Ok (A : out String;
                         B : out Natural)
   with Depends => (A => null,
                    B => A)
   is
   begin
      A := (others => ' ');
      B := A'Length;
   end Test_04_Ok;

   procedure Test_05_Ok (A : out String)
   with Depends => (A => A)
   is
   begin
      A := (others => ' ');
      A (A'First) := 'x';
   end Test_05_Ok;

   --  The customer testcase below.

   type Octet is mod 2**8;
   type Octet_Array is array(Natural range <>) of Octet;

   procedure To_Octet_Array (Text        : String;
                             Data        : out Octet_Array;
                             Octet_Count : out Natural)
   with Depends => (Data        => Text,
                    Octet_Count => (Text, Data))
   is
   begin
      Data := (others => 0);
      Octet_Count := Text'Length;
      if Data'Length < Octet_Count then
         Octet_Count := Data'Length;
      end if;

      for I in Natural range 1 .. Octet_Count loop
         Data(Data'First + I - 1) := Character'Pos(Text(Text'First + I - 1));
      end loop;
   end To_Octet_Array;

end Foo;
