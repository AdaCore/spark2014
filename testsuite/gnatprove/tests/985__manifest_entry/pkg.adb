package body Pkg
  with SPARK_Mode
is
   protected body Box is
      entry Set (X : Integer) when True is
      begin
         Value := X;
      end Set;
   end Box;
end Pkg;
