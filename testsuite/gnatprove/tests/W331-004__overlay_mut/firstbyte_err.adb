with Ada.Text_IO; use Ada.Text_IO;

procedure Firstbyte_Err with SPARK_Mode is

   type Byte is mod 2 ** 8;

   type Integers is range -2 ** 31 ..  2 ** 31 - 1;

   type Arr is array (1 .. 10) of Integers
      with Object_Size => 10 * Integers'Size;

    procedure temp_function1 (input : in Arr;
                output : OUT Byte) with Pre => True is
      type Byte_Ar is array (1 .. 40) of Byte with Object_Size => 40 * Byte'Size;
       dest : aliased constant Byte_Ar with Import, Address => input'Address, Alignment => 4;
    BEGIN
       output := dest (1);
    END temp_function1;

    procedure temp_function2 (input_param : Byte) is
    begin
       Put_Line (Input_Param'Img);
    end;

    A : aliased Arr := (1 .. 10 => 3);
    Tmp : Byte;

begin
  temp_function1 (input => A,
                  output => Tmp);
  temp_function2 (input_param => Tmp);
end;
