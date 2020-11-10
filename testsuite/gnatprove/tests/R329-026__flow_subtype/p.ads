package P with SPARK_Mode is
   package Bad with SPARK_Mode => Off is
      subtype T is Integer;
   end;
   subtype Q is Bad.T; -- should be rejected
end;
