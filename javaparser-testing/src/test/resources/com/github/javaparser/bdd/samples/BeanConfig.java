public class BeanConfig {

  public void setClass(Class<?> cl)
  {
    _cl = cl;

    /*
    if (_name == null)
      _name = Introspector.decapitalize(cl.getSimpleName());
      /*/
  }

  public Class<?> getClassType() { }

  public Bean<?> getComponent() { }

  /**
   * Adds a component binding.
   */
  public void addBinding(Annotation binding) { }

}
