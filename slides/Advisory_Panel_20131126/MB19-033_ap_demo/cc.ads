pragma SPARK_Mode;
package CC
is
   type Days is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

   procedure Next_Day (D : in Days; N : out Days)
     with Contract_Cases =>
       (D = Mon => N = Tue,
        D = Tue => N = Wed,
        D = Wed => N = Thu,
        D = Fri => N = Sat,
        D = Sat => N = Sun);

end CC;
