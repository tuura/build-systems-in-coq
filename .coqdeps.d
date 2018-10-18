src/Data/Maybe.vo src/Data/Maybe.glob src/Data/Maybe.v.beautified: src/Data/Maybe.v src/Data/Functor.vo
src/Data/Maybe.vio: src/Data/Maybe.v src/Data/Functor.vio
src/Data/Functor.vo src/Data/Functor.glob src/Data/Functor.v.beautified: src/Data/Functor.v
src/Data/Functor.vio: src/Data/Functor.v
src/Data/Proxy.vo src/Data/Proxy.glob src/Data/Proxy.v.beautified: src/Data/Proxy.v src/Data/Functor.vo src/Control/Applicative.vo src/Control/Monad.vo
src/Data/Proxy.vio: src/Data/Proxy.v src/Data/Functor.vio src/Control/Applicative.vio src/Control/Monad.vio
src/Data/Monoid.vo src/Data/Monoid.glob src/Data/Monoid.v.beautified: src/Data/Monoid.v
src/Data/Monoid.vio: src/Data/Monoid.v
src/Control/Applicative.vo src/Control/Applicative.glob src/Control/Applicative.v.beautified: src/Control/Applicative.v src/Data/Functor.vo
src/Control/Applicative.vio: src/Control/Applicative.v src/Data/Functor.vio
src/Control/Monad.vo src/Control/Monad.glob src/Control/Monad.v.beautified: src/Control/Monad.v src/Data/Functor.vo src/Control/Applicative.vo
src/Control/Monad.vio: src/Control/Monad.v src/Data/Functor.vio src/Control/Applicative.vio
src/Control/Monad/State.vo src/Control/Monad/State.glob src/Control/Monad/State.v.beautified: src/Control/Monad/State.v src/Data/Functor.vo src/Control/Applicative.vo src/Control/Monad.vo
src/Control/Monad/State.vio: src/Control/Monad/State.v src/Data/Functor.vio src/Control/Applicative.vio src/Control/Monad.vio
src/Data/Functor/Const.vo src/Data/Functor/Const.glob src/Data/Functor/Const.v.beautified: src/Data/Functor/Const.v src/Data/Functor.vo src/Control/Applicative.vo src/Data/Monoid.vo
src/Data/Functor/Const.vio: src/Data/Functor/Const.v src/Data/Functor.vio src/Control/Applicative.vio src/Data/Monoid.vio
src/Prelude.vo src/Prelude.glob src/Prelude.v.beautified: src/Prelude.v
src/Prelude.vio: src/Prelude.v
src/Build.vo src/Build.glob src/Build.v.beautified: src/Build.v src/Build/Task.vo src/Build/Store.vo
src/Build.vio: src/Build.v src/Build/Task.vio src/Build/Store.vio
src/Build/Task.vo src/Build/Task.glob src/Build/Task.v.beautified: src/Build/Task.v src/Data/Maybe.vo src/Data/Functor.vo src/Control/Applicative.vo src/Control/Monad.vo src/Control/Monad/State.vo src/Build/Store.vo src/Prelude.vo
src/Build/Task.vio: src/Build/Task.v src/Data/Maybe.vio src/Data/Functor.vio src/Control/Applicative.vio src/Control/Monad.vio src/Control/Monad/State.vio src/Build/Store.vio src/Prelude.vio
src/Build/Task/Functor.vo src/Build/Task/Functor.glob src/Build/Task/Functor.v.beautified: src/Build/Task/Functor.v src/Data/Functor.vo src/Data/Functor/Const.vo src/Build/Task.vo
src/Build/Task/Functor.vio: src/Build/Task/Functor.v src/Data/Functor.vio src/Data/Functor/Const.vio src/Build/Task.vio
src/Build/Store.vo src/Build/Store.glob src/Build/Store.v.beautified: src/Build/Store.v src/Prelude.vo
src/Build/Store.vio: src/Build/Store.v src/Prelude.vio
src/Build/System.vo src/Build/System.glob src/Build/System.v.beautified: src/Build/System.v src/Data/Maybe.vo src/Data/Functor.vo src/Control/Applicative.vo src/Control/Monad.vo src/Control/Monad/State.vo src/Build.vo src/Build/Task.vo src/Build/Store.vo
src/Build/System.vio: src/Build/System.v src/Data/Maybe.vio src/Data/Functor.vio src/Control/Applicative.vio src/Control/Monad.vio src/Control/Monad/State.vio src/Build.vio src/Build/Task.vio src/Build/Store.vio
