with HAL.Framebuffer; use HAL.Framebuffer;

package Framebuffer_LTDC is

   type Frame_Buffer is abstract limited
     new HAL.Framebuffer.Frame_Buffer_Display with private;

private

   type Frame_Buffer is abstract limited
   new HAL.Framebuffer.Frame_Buffer_Display with null record;

end Framebuffer_LTDC;
