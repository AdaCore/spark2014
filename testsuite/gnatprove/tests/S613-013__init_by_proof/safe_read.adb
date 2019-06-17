with Foo; use Foo;

procedure Safe_Read (Fd : Integer; Buf : out Init_String; Has_Read : out Integer) with SPARK_Mode
is
begin
   Read (Fd, Buf, Has_Read);
end Safe_Read;
