with Pack; use Pack;

package Using is

   procedure P
      with Pre => (X_Is_Positive and then Greater_Than_X (Get_X));

end Using;
