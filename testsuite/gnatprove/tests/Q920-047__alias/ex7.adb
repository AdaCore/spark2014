pragma SPARK_Mode;
procedure Ex7 is
    subtype String5 is String(1..5);
    S : String5;
    procedure P( Str: out String5 ) is
    begin
       Str := "Abcde";
       S   := "Hello";
    end P;
begin
   P(S);
end Ex7;
