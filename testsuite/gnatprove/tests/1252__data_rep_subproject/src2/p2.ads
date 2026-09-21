with P1;

package P2 with SPARK_Mode is

   pragma Assert (P1.My_Rec'Size = 64);

end P2;
