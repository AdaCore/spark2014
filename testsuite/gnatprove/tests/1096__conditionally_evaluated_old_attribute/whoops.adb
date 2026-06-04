pragma Ada_2002;
procedure Whoops with SPARK_Mode is
   E : exception;

   --  Even though Fail always raise an exception, bypassing the post,
   --  the 'Old reference is always conditionally created, in particular
   --  the condition is evaluated before the exception is raised.
   procedure Fail (X : Integer; Y : in out Integer)
     with Post => (if X + 10 >= 20 then Y'Old <= 40), --@OVERFLOW_CHECK:FAIL
       Exceptional_Cases => (E => True);
   procedure Fail (X : Integer; Y : in out Integer) is
   begin
      if X >= 40 or else Y >= 40 then
         raise E;
      end if;
   end Fail;
   X : Integer := Integer'Last;
   Y : Integer := Integer'Last;
begin
   Fail (X, Y);
exception
   when E =>
      null;
end Whoops;
