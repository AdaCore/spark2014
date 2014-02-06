package body Foo
is

   type Dt (Found : Boolean) is record
      case Found is
         when True =>
            Index : Positive;
         when others =>
            null;
      end case;
   end record;

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

   procedure Test_06_Ok (A : out String)
   with Depends => (A => A)
   is
   begin
      Test_05_Ok (A);
   end Test_06_Ok;

   procedure Test_07_Ok (A : out DT)
   with Depends => (A => A)
   is
   begin
      case A.Found is
         when True => A := (Found => True,
                            Index => 1);
         when False => A := (Found => False);
      end case;
   end Test_07_Ok;

   procedure Test_08_Ok (A : out DT)
   with Depends => (A => A)
   is
   begin
      Test_07_Ok (A);
   end Test_08_Ok;

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
