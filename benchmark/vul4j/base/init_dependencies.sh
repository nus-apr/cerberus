#!/bin/bash

if [[ $# -eq 0 ]] ; then
    echo -e "No args supplied.\nUsage: $0 [path_to_java_projects_target_dir]"
    exit 1
fi


TARGET_PATH=$1
DEPENDENCY_PATH=$TARGET_PATH/dependency
EXTRACTED_DEPENDENCIES_PATH=$TARGET_PATH/extracted_dependencies

rm -rf "$EXTRACTED_DEPENDENCIES_PATH" \
  && mkdir "$EXTRACTED_DEPENDENCIES_PATH" \
    && cd "$EXTRACTED_DEPENDENCIES_PATH" \
&& echo "Extract all dependencies from the 'jar' files from $DEPENDENCY_PATH ..." \
    && find "$DEPENDENCY_PATH" -type f -name "*.jar" -exec jar -xf {} \;

echo "Delete *.RSA *.DSA *.SF signature files..." \
  && find . -type f \( -name "*.RSA" -o -name "*.DSA" -o -name "*.SF" \) -delete

echo "Merge all dependencies into a single 'jar' file..." \
  && jar -cf "$TARGET_PATH"/all-dependencies.jar . \
    && echo "JAR File with all dependencies successfully created: $TARGET_PATH/all-dependencies.jar"