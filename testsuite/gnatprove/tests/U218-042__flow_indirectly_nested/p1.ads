package P1 with Abstract_State => S1 is
private
   package P2 is
      package P3 with Abstract_State => (S3 with Part_Of => S1) is
         procedure Me3;
      end;
   end;
end;
