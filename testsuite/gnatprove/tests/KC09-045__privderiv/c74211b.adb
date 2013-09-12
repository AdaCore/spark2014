procedure C74211B is 

    package P1 is
         type Lt1 is limited private;
         function Lt1_Value_2 return Lt1;
    private
         type Lt1 is range 1 .. 10;
    end P1;

    use P1;

    package P2 is
         type Lt3 is limited private;
    private
         type Lt3 is new Lt1;
 end P2;

    package body P1 is

         function Lt1_Value_2 return Lt1 is
         begin
              return 2;
         end Lt1_Value_2;

    end P1;

    package body P2 is
         function U return Lt3 is
         begin
              return Lt1_Value_2;
         end U;

    end P2;
 begin
  null;
end C74211B;
