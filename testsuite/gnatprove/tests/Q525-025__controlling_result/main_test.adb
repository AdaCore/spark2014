-- Test proof issues with array lengths in contracts and concatenation.
pragma SPARK_Mode;

with Ada.Streams;
with Fixed_String;
with Fixed_Stream;

procedure Main_Test is

    use type Ada.Streams.Stream_Element_Array;

    Field_10 : Fixed_String.Object := Fixed_String.Create(10, "Long");
    Field_06 : Fixed_String.Object := Fixed_String.Create(6, "Short");

    Stream_10: Fixed_Stream.Object := Fixed_Stream.Create(10, "Long");
    Stream_06: Fixed_Stream.Object := Fixed_Stream.Create(6, "Short");

    Ref_String  : String := "abcdefghijkl";
    Short_String: String := "foo";

    Len_N: Natural;
    Len_I: Integer;
    Len_L: Long_Integer;

    Total_Len   : Natural;
    Total_String: String := Field_10.Null_String & Field_06.Null_String;
    -- range check
    Total_Stream: Ada.Streams.Stream_Element_Array :=
                    Stream_10.Null_String & Stream_06.Null_String;
    -- range check

begin
    pragma Assert( Field_10.Elements = 10 ); -- not provable
    pragma Assert( Field_06.Elements =  6 ); -- not provable

    Len_N := Total_Stream'Length; -- range check
    Len_I := Total_Stream'Length; -- OK
    Len_L := Total_Stream'Length; -- OK
    Len_N := Total_String'Length; -- OK
    Len_I := Total_String'Length; -- OK
    Len_L := Total_String'Length; -- OK

    -- test string operations
    Total_Len    := Field_10.Elements + Field_06.Elements; -- OK

    Total_String := Field_10.Convert( Ref_String ) &
                    Field_06.Convert( Short_String ); -- length check

--    pragma Assert( Total_String'Length = 16 ); -- not provable
    pragma Assert( Total_String'Length = Total_Len ); -- not provable

    -- test stream operations
    Total_Len    := Stream_10.Elements + Stream_06.Elements; -- overflow

    Total_Stream := Stream_10.Convert( Ref_String ) &
                    Stream_06.Convert( Short_String ); -- length check

    Len_N := Total_Stream'Length; -- OK
    Len_I := Total_Stream'Length; -- OK
    Len_L := Total_Stream'Length; -- OK
    Len_N := Total_String'Length; -- OK
    Len_I := Total_String'Length; -- OK
    Len_L := Total_String'Length; -- OK

end Main_Test;
