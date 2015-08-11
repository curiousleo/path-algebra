for f in `find -type f -name '*.agda' | sed 's#^\./\(.*\)\.agda#\1#' | sed 's#/#\.#g'`; do
  if [ "$f" != "Everything" ]; then
    echo "open import $f"
  fi
done
