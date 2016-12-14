with P1; --  declare first  task object \
                                         -- conflict
with P2; --  declare second task object /

procedure Main with SPARK_Mode => Off is
begin
   null;
end;
