with Foo; use Foo;

procedure Safe_Read_Str (Fd : Integer; Buf : out String; Has_Read : out Integer) with SPARK_Mode
is
begin
   Read_Str (Fd, Buf, Has_Read);
end Safe_Read_Str;
