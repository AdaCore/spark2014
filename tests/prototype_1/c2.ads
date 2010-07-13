with Data_Model;
with C3;

package C2 is

--     type Servant_T is record
--        C3_Servant : C3.Servant_T;
--     end record;

   procedure I1
     (-- Servant : in out Servant_T;
      Param_1 : in Data_Model.Int32_T;
      Param_2 : in Data_Model.Int32_T; --  out
      Param_3 : out Data_Model.Int32_T);

   procedure I2
     (-- Servant : in out Servant_T;
      Param_1 : in Data_Model.Int32_T;
      Param_2 : out Data_Model.Int32_T);

end C2;
