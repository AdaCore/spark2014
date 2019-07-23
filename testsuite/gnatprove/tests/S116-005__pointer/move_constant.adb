procedure Move_Constant
  with SPARK_Mode
is
    type Ptr is access Integer;

    procedure Bad (X : Ptr; Y : out Ptr) with
      Pre => True
    is
    begin
       Y := X;
    end Bad;

begin
   null;
end Move_Constant;
